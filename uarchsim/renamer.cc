#include "renamer.h"
#include <cassert>
#include <cstdio>
#include <cmath>  
////////////////////////////////// CONSTRUCTOR ////////////////////////////////

renamer::renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches, uint64_t n_active,bool vp_perf,int vpq_size,bool vp_oracle_conf,int svp_index_bits,int svp_tag_bits,int vp_confmax,int vp_eligible_intalu,int vp_eligible_fpalu,int vp_eligible_load,bool gshare_en,int gshare_index, int gshare_tag,int gshare_confmax, int gshare_history)
{
    logical_reg_count = n_log_regs;
    physical_reg_count = n_phys_regs;
    unresolved_branch_count = n_branches;
    active_list_size = n_active;

    // gshare-VP initialization
    gshare_enabled       = gshare_en;
    this->gshare_index      = gshare_index;
    this->gshare_tag      = gshare_tag;
    gshare_conf_max      = gshare_confmax;
    this->gshare_history = gshare_history;
    c_ghr        = 0;
     
    if (gshare_enabled) {
        gshare_vp = new gshare_vp_struct[1 << gshare_index];
        for (int i = 0; i < (1 << gshare_index); i++)
        {
            gshare_vp[i].valid = 0;
            gshare_vp[i].tag = 0;
            gshare_vp[i].value = 0;
            gshare_vp[i].conf = 0;
        }
    }
        
    ///////////////////////Value Prediction

    svp = new svp_struct[1<<svp_index_bits];
    vpq.vpq_data = new vpq_data_struct[vpq_size];
    this->vpq_size = vpq_size;
    this->vp_eligible_intalu = vp_eligible_intalu;
    this->vp_eligible_fpalu = vp_eligible_fpalu;

    this->vp_eligible_load = vp_eligible_load;

    vpq.h=0;
    vpq.t=0;
    vpq.h_phase=0;
    vpq.t_phase=0;
    vp_perfect = vp_perf;
    vp_oracle =vp_oracle_conf;
    svp_index = svp_index_bits;
    svp_tag = svp_tag_bits;
    vp_conf = vp_confmax;
    //printf("\nValue Prediction Values:vp_perfect %d vp_oracle %d svp_index%d svp_tag %d vp_conf %d vp_size %d\n",vp_perfect,vp_oracle,svp_index,svp_tag,vp_conf,vpq_size);
     
    for (int i=0;i<1<<svp_index_bits;i++)
    {
        svp[i].valid=0;
	    svp[i].tag=0;
    	svp[i].conf=0;
	    svp[i].last_value=0;
	    svp[i].stride=0;
	    svp[i].instance=0;
    }
    for(int i=0;i<vpq_size;i++)
    {
        vpq.vpq_data[i].value=0;
        vpq.vpq_data[i].pc=0;
    }

    ////////////// Struct init ///////////////
    rmt = new uint64_t[logical_reg_count];
    amt = new uint64_t [logical_reg_count];

    // Initialize RMT and AMT
    for (uint64_t i = 0; i < logical_reg_count; i++) 
    {
        rmt[i] = i;
        amt[i] = i;
    }

    // Initialize free list
    free_list.size = physical_reg_count - logical_reg_count;
    free_list.ft = new uint64_t [free_list.size];
    free_list.head = 0;
    free_list.tail = 0;
    free_list.h_phase = 0;
    free_list.t_phase = 1;

    for (uint64_t i = 0; i < free_list.size; i++) 
    {
        free_list.ft[i] = logical_reg_count + i; 
    }

    active_list.at = new Active_List_struct[active_list_size];
    active_list.size = active_list_size;

    prf = new uint64_t[physical_reg_count];
    prf_ready_bit = new bool[physical_reg_count];
    for (uint64_t i = 0; i < logical_reg_count; i++) 
    {
        prf_ready_bit[i] = true;
    }

    branch_cp = new branch_checkpoint[unresolved_branch_count];
    for(uint64_t i = 0; i < unresolved_branch_count; i++)
    {
        branch_cp[i].rmt = new uint64_t[logical_reg_count];
    }
    GBM = 0;
}

/////////////////////////////////DESTRUCTOR//////////////////////////////

renamer::~renamer()
{
    delete[] rmt;
    delete[] amt;
    delete[] free_list.ft;
    delete[] active_list.at;
    for(uint64_t i = 0; i < unresolved_branch_count; i++)
    {
        delete[] branch_cp[i].rmt;
    }
 }


 /////////////////////// FUNCTIONS //////////////////////////////////////////

bool renamer::stall_reg(uint64_t bundle_dst)
{
    uint64_t free_count;
    if(free_list.h_phase == free_list.t_phase)
    {
        free_count = free_list.tail - free_list.head;
    }
    else
    {
        free_count = free_list.size - (free_list.head - free_list.tail);
    }
    
    if(free_count >= bundle_dst)
    {
        return false;
    }
    else
    {
        return true;
    }
}


bool renamer::stall_branch(uint64_t bundle_branch)
{
    uint64_t free_branch_count = 0;
    for(uint64_t i = 0; i < unresolved_branch_count; i++)
    {
        if((GBM & (1ULL << i)) == 0)
        {
            free_branch_count++;
        }
    }
    return (free_branch_count < bundle_branch);
}

uint64_t renamer::get_branch_mask()
{
    return GBM;
}

uint64_t renamer::rename_rsrc(uint64_t log_reg)
{
    return (rmt[log_reg]);
}

uint64_t renamer::rename_rdst(uint64_t log_reg)
{
    uint64_t physical_reg = free_list.ft[free_list.head];
    free_list.head++;
    if(free_list.head == free_list.size)
    {
        free_list.head = 0;
        free_list.h_phase = !free_list.h_phase;
    }
    rmt[log_reg] = physical_reg;
    prf_ready_bit[physical_reg] = false; 
    return physical_reg;
}

void renamer::increment_svp_instance(uint64_t pc)
{
    uint64_t index = (pc >> 2) & ((1ULL << svp_index) - 1);
    uint64_t tag   = (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);
    svp[index].instance++;
}

uint64_t renamer::checkpoint()
{
    ///// Find free bit position in GBM
    uint64_t bit_position;

    for(uint64_t i = 0; i < unresolved_branch_count; i++)
    {
        if((GBM & (1ULL << i)) == 0)
        {
            bit_position = i;
            branch_cp[i].GBM = GBM;

            GBM = (GBM | (1ULL << i));

            for(int j = 0; j < logical_reg_count; j++)
            {
                branch_cp[i].rmt[j] = rmt[j];
            }

            branch_cp[i].fl_head = free_list.head;
            branch_cp[i].fl_h_phase = free_list.h_phase;
	        branch_cp[i].vpq_t = vpq.t;
            branch_cp[i].vpq_t_phase = vpq.t_phase;
            break;
        }
    }
    return bit_position;
}



bool renamer::stall_dispatch(uint64_t bundle_inst)
{
    if(active_list.head == active_list.tail)
    {
        if(active_list.h_phase == active_list.t_phase)
        {
            return false;
        }
        else
        {
            return true;
        }
    }
    else
    {
        uint64_t free_count;
        if(active_list.h_phase == active_list.t_phase)
        {
            free_count = active_list.size - (active_list.tail - active_list.head);
        }
        else
        {
            free_count = active_list.head - active_list.tail;
        }
        
        if(free_count >= bundle_inst)
        {
            return false;
        }
        else
        {
            return true;
        }
    }
}

uint64_t renamer::dispatch_inst(bool dest_valid,uint64_t log_reg,uint64_t phys_reg,bool load,bool store,bool branch,bool amo,bool csr,bool branch_predicted_taken,uint64_t PC)
{
    assert(!stall_dispatch(1) && "Active List full during dispatch!");
    uint64_t index = active_list.tail;
    active_list.at[index].dst_flag = dest_valid;

    if(active_list.at[index].dst_flag)
    {
        active_list.at[index].logical_dst_reg = log_reg;
        active_list.at[index].physical_dst_reg = phys_reg;
    }
    active_list.at[index].completioin_flag = 0;
    active_list.at[index].exp_flag = 0;
    active_list.at[index].load_violation_flag = 0;
    active_list.at[index].value_mispred_flag = 0;
    active_list.at[index].branch_mispred_flag = 0;
    active_list.at[index].vp_eligible = 0;
    active_list.at[index].vp_no_pred = 0;
    active_list.at[index].vp_conf = 0;
    active_list.at[index].vp_pred_correct = 1; 
    active_list.at[index].load_flag = load;
    active_list.at[index].store_flag = store;
    active_list.at[index].branch_flag = branch;
    active_list.at[index].amo_flag = amo;
    active_list.at[index].csr_flag = csr;
    active_list.at[index].branch_predicted_taken = branch_predicted_taken;
    active_list.at[index].pc = PC;
    
    active_list.tail++;
    if(active_list.tail == active_list.size)
    {
        active_list.tail = 0;
        active_list.t_phase = !active_list.t_phase;
    }
    return index;
}

bool renamer::is_ready(uint64_t phys_reg)
{
    return prf_ready_bit[phys_reg];
}

void renamer::clear_ready(uint64_t phys_reg)
{
    prf_ready_bit[phys_reg] = false;
}

uint64_t renamer::read(uint64_t phys_reg)
{
    return prf[phys_reg];
}

void renamer::set_ready(uint64_t phys_reg)
{
    prf_ready_bit[phys_reg] = true;
}

void renamer::write(uint64_t phys_reg, uint64_t value)
{
    prf[phys_reg] = value;
}

void renamer::set_complete(uint64_t AL_index)
{
    active_list.at[AL_index].completioin_flag = true;
}

void renamer::resolve(uint64_t AL_index, uint64_t branch_ID, bool correct)
{
    if(correct)
    {
        GBM = GBM & (~(1ULL << branch_ID));
        for(int i = 0; i < unresolved_branch_count; i++)
        {
            branch_cp[i].GBM = branch_cp[i].GBM & (~(1ULL << branch_ID));
        }
    }
    else
    {
        GBM = branch_cp[branch_ID].GBM;
        for(int i = 0; i < unresolved_branch_count; i++)
        {
            branch_cp[i].GBM = branch_cp[i].GBM & (~(1ULL << branch_ID));
        }

        for(int i = 0; i < logical_reg_count; i++)
        {
            rmt[i] = branch_cp[branch_ID].rmt[i];
        }

        free_list.head = branch_cp[branch_ID].fl_head;
        free_list.h_phase = branch_cp[branch_ID].fl_h_phase;

        active_list.tail = AL_index + 1;
        if (active_list.tail == active_list.size)
        {
            active_list.tail = 0;
        }
        
        if(active_list.head >= active_list.tail)
        {
            active_list.t_phase = !active_list.h_phase;
        }
        else
        {
            active_list.t_phase = active_list.h_phase;
        }
	    uint64_t temp = branch_cp[branch_ID].vpq_t;
        bool temp_phase = branch_cp[branch_ID].vpq_t_phase;

        while (temp != vpq.t || temp_phase != vpq.t_phase)
        {
            uint64_t pc = vpq.vpq_data[temp].pc;
            uint64_t s_index = (pc >> 2) & ((1ULL << svp_index) - 1);
            uint64_t s_tag = (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);
            
            if (check_svp(pc))
            {
                if (svp[s_index].instance > 0)
                {
                    svp[s_index].instance--;
                }
            }
            
            temp++;
            if (temp == (uint64_t)vpq_size)
            {
                temp = 0;
                temp_phase = !temp_phase;
            }
        }
        vpq.t = branch_cp[branch_ID].vpq_t;
        vpq.t_phase = branch_cp[branch_ID].vpq_t_phase;
    }
}


bool renamer::precommit(bool &completed, bool &exception, bool &load_viol, bool &br_misp, bool &val_misp, bool &load, bool &store, bool &branch, bool &amo, bool &csr, uint64_t &PC)
{
    if(active_list.head == active_list.tail && active_list.t_phase == active_list.h_phase)
    {
        return false;
    }
    else
    {
        uint64_t index = active_list.head;
        completed = active_list.at[index].completioin_flag;
        exception = active_list.at[index].exp_flag;
        load_viol = active_list.at[index].load_violation_flag;
        br_misp = active_list.at[index].branch_mispred_flag;
        val_misp = active_list.at[index].value_mispred_flag;
        load = active_list.at[index].load_flag;
        store = active_list.at[index].store_flag;
        branch = active_list.at[index].branch_flag;
        amo = active_list.at[index].amo_flag;
        csr = active_list.at[index].csr_flag;
        PC = active_list.at[index].pc;
        return  true;
    }
}

void renamer::commit()
{
    // Active List must not be empty
    assert(!(active_list.head == active_list.tail && active_list.h_phase == active_list.t_phase));

    uint64_t index = active_list.head;

    // Commit must be legal
    assert(active_list.at[index].completioin_flag);
    assert(!active_list.at[index].exp_flag);
    assert(!active_list.at[index].load_violation_flag);

    uint64_t amt_index = active_list.at[index].logical_dst_reg;
    
    if(active_list.at[index].dst_flag)
    {
        free_list.ft[free_list.tail] = amt[amt_index];
        free_list.tail++;
        if(free_list.tail == free_list.size)
        {
            free_list.tail = 0;
            free_list.t_phase = !free_list.t_phase;
        }
        amt[amt_index] = active_list.at[index].physical_dst_reg;
    }
    
    if (active_list.at[index].vp_eligible)
    {
        vp_eligible_count++;
        if (active_list.at[index].vp_no_pred)
        {
            vp_miss++;
        }
        else
        {
            if (active_list.at[index].vp_conf == vp_conf)
            {
                vp_conf_corr++;  // Count ALL confident predictions
                if (!active_list.at[index].vp_pred_correct)
                {
                    vp_conf_incorr++;  // Also count incorrect ones separately
                }
            }
            else
            {
                if (active_list.at[index].vp_pred_correct)
                {
                    vp_unconf_corr++;
                }
                else
                {
                    vp_unconf_incorr++;	  
                }
            }
        }
    }
    else
    {
        vp_n_eligible_count++;
    }
    if (active_list.at[index].vp_eligible && !vp_perfect)
    {
            int vpq_index = vpq.h;
            uint64_t s_index = (active_list.at[index].pc >> 2) & ((1ULL << svp_index) - 1); 
            uint64_t s_tag = (active_list.at[index].pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1); 

            if (check_svp(active_list.at[index].pc))
            {
                int64_t new_stride = (int64_t)vpq.vpq_data[vpq_index].value - (int64_t)svp[s_index].last_value;
	            if (new_stride == svp[s_index].stride)
                {
                    svp[s_index].conf++;
	                if (svp[s_index].conf>=vp_conf)
                    {
	                    svp[s_index].conf=vp_conf;
	                }
	            }
	            else
                {
                    svp[s_index].stride=new_stride;
	                svp[s_index].conf=0;
	            }
                svp[s_index].last_value=vpq.vpq_data[vpq_index].value;
	            svp[s_index].instance--;
            }
            else
            {
                int svp_instance=0;
		        svp[s_index].valid=1;
		        svp[s_index].conf=0;
		        if (gshare_enabled) svp[s_index].stride=0;  
                        else svp[s_index].stride=vpq.vpq_data[vpq_index].value;		
		        svp[s_index].last_value=vpq.vpq_data[vpq_index].value;
		        svp[s_index].tag = s_tag;
		        int temph = vpq.h;
		        for (int i=1;i<vpq_size;i++)   
                {
                    temph = (vpq.h+i)%vpq_size;
			        if (temph==vpq.t)
                    {
			            break;
			        }
			        if (active_list.at[index].pc == vpq.vpq_data[temph].pc)
                    {
                        svp_instance++;
			        }
		        }
		        svp[s_index].instance=svp_instance;
            }
        vpq.h++;
        if(vpq.h == vpq_size)
        {
            vpq.h = 0;
            vpq.h_phase = !vpq.h_phase;
        }
        if (gshare_enabled)
        {
            train_gshare(active_list.at[index].pc, vpq.vpq_data[vpq_index].ghr, vpq.vpq_data[vpq_index].value);
        }
    }
    if (active_list.at[index].branch_flag && gshare_enabled)
    {
        bool actual_taken = active_list.at[index].branch_predicted_taken ^ active_list.at[index].branch_mispred_flag;
        update_c_ghr(actual_taken);
    }
    active_list.head++;
    if(active_list.head == active_list.size)
    {
        active_list.head = 0;
        active_list.h_phase = !active_list.h_phase;
    }
}

void renamer::squash()
{
    for (uint64_t i = 0; i < logical_reg_count; i++)
    {
        rmt[i] = amt[i];
    }

    free_list.head = free_list.tail;
    free_list.h_phase = !free_list.t_phase;

    active_list.tail = active_list.head;
    active_list.t_phase = active_list.h_phase;

    GBM = 0;
    
    uint64_t temp = vpq.h;
    bool temp_phase = vpq.h_phase;

    while (temp != vpq.t || temp_phase != vpq.t_phase)
    {
        uint64_t pc = vpq.vpq_data[temp].pc;
        uint64_t s_index = (pc >> 2) & ((1ULL << svp_index) - 1);
        uint64_t s_tag = (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);
        
        if (check_svp(pc))
        {
            if (svp[s_index].instance > 0)
            {
                svp[s_index].instance--;
            }
        }
        
        temp++;
        if (temp == (uint64_t)vpq_size)
        {
            temp = 0;
            temp_phase = !temp_phase;
        }
    }
    vpq.t=vpq.h;
    vpq.t_phase=vpq.h_phase;
}


void renamer::set_exception(uint64_t AL_index)
{
    active_list.at[AL_index].exp_flag = true;
}

void renamer::set_load_violation(uint64_t AL_index)
{
    active_list.at[AL_index].load_violation_flag = true;
}

void renamer::set_branch_misprediction(uint64_t AL_index)
{
    active_list.at[AL_index].branch_mispred_flag = true;
}

void renamer::set_value_misprediction(uint64_t AL_index)
{
    active_list.at[AL_index].value_mispred_flag = true;
}

bool renamer::get_exception(uint64_t AL_index)
{
    return active_list.at[AL_index].exp_flag;
}

bool renamer::stall_vpq(uint64_t bundle_vp_eligible)
{
    if(vpq.h == vpq.t)
    {
        if(vpq.h_phase == vpq.t_phase)
        {
            return false;
        }
        else
        {
            return true;
        }
    }
    else
    {
        uint64_t free_count;
        if(vpq.h_phase == vpq.t_phase)
        {
            free_count = vpq_size - (vpq.t - vpq.h);
        }
        else
        {
            free_count = vpq.h - vpq.t;
        }
        
        if(free_count >= bundle_vp_eligible)
        {
            return false;
        }
        else
        {
            return true;
        }
    }
}

uint64_t renamer::vpq_update(uint64_t pc)
{
    uint64_t index = vpq.t;
    vpq.vpq_data[index].pc = pc;
    vpq.vpq_data[index].ghr = c_ghr; 
    
    vpq.t++;
    if(vpq.t == vpq_size)
    {
        vpq.t = 0;
        vpq.t_phase = !vpq.t_phase;
    }
    return index;
}

bool renamer::check_svp (uint64_t pc)
{
	if (svp_tag==0)
    {
	    return 1;
	}
    uint64_t index = (pc >> 2) & ((1ULL << svp_index) - 1);;
    uint64_t tag =  (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);;
    if (svp[index].valid && (svp[index].tag==tag || svp_tag==0))
    {
      return 1;
    }
    else
    {
      return 0;
    }
}

uint64_t renamer::get_svp_index(uint64_t pc)
{
      return (pc >> 2) & ((1ULL << svp_index) - 1);;
}

bool renamer::is_vp_perfect()
{
    return vp_perfect;
}

bool renamer::is_vp_oracle()
{
    return vp_oracle;
}

uint64_t renamer::get_prediction_value(uint64_t index)
{
    return (uint64_t)((int64_t)svp[index].last_value + svp[index].stride*svp[index].instance);
}
void renamer::vp_active_list_update(uint64_t AL_index,int vp_eligible, int vp_conf,int vp_pred)
{
    active_list.at[AL_index].vp_eligible = vp_eligible;
	active_list.at[AL_index].vp_conf =  vp_conf;
    active_list.at[AL_index].vp_no_pred = (vp_pred==0); 
	
}
void renamer::vp_active_list_pred_no_correct(uint64_t AL_index)
{
       active_list.at[AL_index].vp_pred_correct=0;
}



int renamer::get_vp_conf()
{
	return vp_conf;
}
void renamer::set_vpq_value(uint64_t index,uint64_t value)
{
	vpq.vpq_data[index].value=value;
}
int renamer::get_svp_conf(uint64_t index)
{
	return svp[index].conf;
}	

void renamer::dump_stats(FILE *fp)
{
    uint64_t total = vp_eligible_count + vp_n_eligible_count;
    
    fprintf(fp, "VPU MEASUREMENTS-----------------------------------\n");
    fprintf(fp, "vpmeas_ineligible         : %10lu (%6.2f%%) // Not eligible for value prediction.\n", 
            vp_n_eligible_count, 100.0 * vp_n_eligible_count / total);
    fprintf(fp, "vpmeas_eligible           : %10lu (%6.2f%%) // Eligible for value prediction.\n", 
            vp_eligible_count, 100.0 * vp_eligible_count / total);
    fprintf(fp, "   vpmeas_miss            : %10lu (%6.2f%%) // VPU was unable to generate a value prediction (e.g., SVP miss).\n", 
            vp_miss, 100.0 * vp_miss / total);
    fprintf(fp, "   vpmeas_conf_corr       : %10lu (%6.2f%%) // VPU generated a confident and correct value prediction.\n", 
            vp_conf_corr - vp_conf_incorr, 100.0 * (vp_conf_corr - vp_conf_incorr) / total);
    fprintf(fp, "   vpmeas_conf_incorr     : %10lu (%6.2f%%) // VPU generated a confident and incorrect value prediction. (MISPREDICTION)\n", 
            vp_conf_incorr, 100.0 * vp_conf_incorr / total);
    fprintf(fp, "   vpmeas_unconf_corr     : %10lu (%6.2f%%) // VPU generated an unconfident and correct value prediction. (LOST OPPORTUNITY)\n", 
            vp_unconf_corr, 100.0 * vp_unconf_corr / total);
    fprintf(fp, "   vpmeas_unconf_incorr   : %10lu (%6.2f%%) // VPU generated an unconfident and incorrect value prediction.\n", 
            vp_unconf_incorr, 100.0 * vp_unconf_incorr / total);
}

void renamer::dump_init_stats(FILE *fp){
    // Calculate bits for conf field: ceil(log2(confmax+1))
    uint64_t conf_bits = (uint64_t)ceil(log2((double)(vp_conf + 1)));
    // Calculate bits for instance counter: ceil(log2(VPQsize))
    uint64_t instance_bits = (uint64_t)ceil(log2((double)vpq_size));
    // Bits per SVP entry
    uint64_t bits_per_entry = svp_tag + conf_bits + 64 + 64 + instance_bits;  // tag + conf + retired_value + stride + instance
    // Total SVP entries
    uint64_t svp_entries = 1ULL << svp_index;
    // Total storage cost
    uint64_t total_bits = svp_entries * bits_per_entry;
    double total_bytes = (double)total_bits / 8.0;
    double total_kb = total_bytes / 1024.0;

    fprintf(fp, "\n=== VALUE PREDICTOR ============================================================\n\n");
    
    fprintf(fp, "VP-eligible configuration:\n");
    fprintf(fp, "   predINTALU = %d\n", vp_eligible_intalu);
    fprintf(fp, "   predFPALU  = %d\n", vp_eligible_fpalu);
    fprintf(fp, "   predLOAD   = %d\n", vp_eligible_load);
    fprintf(fp, "\n");

    
    if (!vp_perfect)
    {
        fprintf(fp, "VALUE PREDICTOR = stride (Project 4 spec. implementation)\n");
        fprintf(fp, "   VPQsize         = %d\n", vpq_size);
        fprintf(fp, "   oracleconf      = %d (%s)\n", vp_oracle, vp_oracle ? "oracle confidence" : "real confidence");
        fprintf(fp, "   # index bits    = %d\n", svp_index);
        fprintf(fp, "   # tag bits      = %d\n", svp_tag);
        fprintf(fp, "   confmax         = %d\n", vp_conf);
    }
    else
    {
        fprintf(fp, "VALUE PREDICTOR = perfect\n");
    }
    fprintf(fp, "\n");

    fprintf(fp, "COST ACCOUNTING\n");
    if(!vp_perfect){
    fprintf(fp, "   One SVP entry:\n");
    fprintf(fp, "      tag           : %3d bits  // num_tag_bits\n", svp_tag);
    fprintf(fp, "      conf          : %3lu bits  // formula: (uint64_t)ceil(log2((double)(confmax+1)))\n", conf_bits);
    fprintf(fp, "      retired_value :  64 bits  // RISCV64 integer size.\n");
    fprintf(fp, "      stride        :  64 bits  // RISCV64 integer size. Competition opportunity: truncate stride to far fewer bits based on stride distribution of stride-predictable instructions.\n");
    fprintf(fp, "      instance ctr  : %3lu bits  // formula: (uint64_t)ceil(log2((double)VPQsize))\n", instance_bits);
    fprintf(fp, "      -------------------------\n");
    fprintf(fp, "      bits/SVP entry: %3lu bits\n", bits_per_entry);
    fprintf(fp, "   Total storage cost (bits) = (%lu SVP entries x %lu bits/SVP entry) = %lu bits\n", svp_entries, bits_per_entry, total_bits);
    fprintf(fp, "   Total storage cost (bytes) = %.2f B (%.2f KB)\n", total_bytes, total_kb);
    }
    else
    {
        fprintf(fp, "  Impossible.\n");
    }
}


uint64_t renamer::gshare_index_hash(uint64_t pc, uint64_t ghr, int index, int history)
{
    uint64_t masked_ghr = ghr & ((1ULL << history) - 1);
    return ((pc >> 2) ^ masked_ghr) & ((1ULL << index) - 1);
}

uint64_t renamer::gshare_tag_hash(uint64_t pc, uint64_t ghr, int index, int tag, int history)
{
    if (tag == 0) return 0;
    uint64_t masked_ghr = ghr & ((1ULL << history) - 1);
    return (((pc >> 2) >> index) ^ masked_ghr) & ((1ULL << tag) - 1);
}

bool renamer::is_gshare_enabled()
{
    return gshare_enabled;
}

uint64_t renamer::get_c_ghr()
{
    return c_ghr;
}

void renamer::update_c_ghr(bool taken)
{
    c_ghr = ((c_ghr << 1) | (taken ? 1 : 0)) & ((1ULL << gshare_history) - 1);
}

bool renamer::gshare_hit_confidence(uint64_t pc, uint64_t ghr)
{
    if (!gshare_enabled) return false;
    uint64_t index = gshare_index_hash(pc, ghr, gshare_index, gshare_history);
    if (!gshare_vp[index].valid)
    {
        return false;
    }
    if (gshare_tag > 0)
    {
        uint64_t tag = gshare_tag_hash(pc, ghr, gshare_index, gshare_tag, gshare_history);
        if (gshare_vp[index].tag != tag)
        {
            return false;
        }
    }
    return (gshare_vp[index].conf == gshare_conf_max);
}

uint64_t renamer::get_gshare_prediction(uint64_t pc, uint64_t ghr)
{
    uint64_t index = gshare_index_hash(pc, ghr, gshare_index, gshare_history);
    return gshare_vp[index].value;
}

void renamer::train_gshare(uint64_t pc, uint64_t ghr, uint64_t value)
{
    if (!gshare_enabled) return;
    uint64_t index = gshare_index_hash(pc, ghr, gshare_index, gshare_history);
    uint64_t tag = gshare_tag_hash(pc, ghr, gshare_index, gshare_tag, gshare_history);

    if (gshare_vp[index].valid && (gshare_tag == 0 || gshare_vp[index].tag == tag))
    {
        if (gshare_vp[index].value == value)
        {
            if (gshare_vp[index].conf < gshare_conf_max)
            {
                gshare_vp[index].conf++;
            }
        }
        else
        {
            if (gshare_vp[index].conf > 0)
            {
                gshare_vp[index].conf--;
            }
            else
            {
                gshare_vp[index].value = value;
            }
        }
    }
    else
    {
        gshare_vp[index].valid = 1;
        gshare_vp[index].tag = tag;
        gshare_vp[index].value = value;
        gshare_vp[index].conf = 0;
    }
}

#include "renamer.h"
#include <cassert>
#include <cstdio>
////////////////////////////////// CONSTRUCTOR ////////////////////////////////

renamer::renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches, uint64_t n_active,bool vp_perf,int vpq_size,bool vp_oracle_conf,int svp_index_bits,int svp_tag_bits,int vp_confmax)
{
    logical_reg_count = n_log_regs;
    physical_reg_count = n_phys_regs;
    unresolved_branch_count = n_branches;
    active_list_size = n_active;

    //////////////////////////////////////////
    // Value Prediction
    /////////////////////////////////////////
    svp = new svp_struct[1<<svp_index_bits];
    vpq.vpq_data = new vpq_data_struct[vpq_size];
    this->vpq_size = vpq_size;
    vpq.h=0;
    vpq.t=0;
    vpq.h_phase=0;
    vpq.t_phase=1;
    vp_perfect = vp_perf;
    vp_oracle =vp_oracle_conf;
    svp_index = svp_index_bits;
    svp_tag = svp_tag_bits;
    vp_conf = vp_confmax;
    printf("\nValue Prediction Values:vp_perfect %d vp_oracle %d svp_index%d svp_tag %d vp_conf %d vp_size %d\n",vp_perfect,vp_oracle,svp_index,svp_tag,vp_conf,vpq_size);
     

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
    //prf_ready_bit[physical_reg] = false; 

    return physical_reg;

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

uint64_t renamer::dispatch_inst(bool dest_valid,uint64_t log_reg,uint64_t phys_reg,bool load,bool store,bool branch,bool amo,bool csr,uint64_t PC)
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
    
    active_list.at[index].load_flag = load;
    active_list.at[index].store_flag = store;
    active_list.at[index].branch_flag = branch;
    active_list.at[index].amo_flag = amo;
    active_list.at[index].csr_flag = csr;
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
    
    if (active_list.at[index].vp_eligible){
       int vpq_index = vpq.h;
       int svp_index = (active_list.at[index].pc >> 2) & ((1ULL << (svp_index)) - 1); 
       int svp_tag = (active_list.at[index].pc >> svp_index) & ((1ULL << (svp_tag)) - 1); 

       if (svp[svp_index].valid && svp[svp_index].tag == svp_tag){
            int new_stride = vpq.vpq_data[vpq_index].value - svp[svp_index].last_value;
	    if (new_stride == svp[svp_index].stride){
	      svp[svp_index].conf++;
	      if (svp[svp_index].conf>=3){
	          svp[svp_index].conf=3;
	      }
	    
	    }else{
	       svp[svp_index].stride=new_stride;
	       svp[svp_index].conf=0;
	    }
       
       }else{
	           int svp_instance=0;
		   svp[svp_index].valid=1;
		   svp[svp_index].conf=0;
		   svp[svp_index].stride=vpq.vpq_data[vpq_index].value;
		   svp[svp_index].last_value=vpq.vpq_data[vpq_index].value;
		   svp[svp_index].tag = svp_tag;
		   int temph = vpq.h;
		   for (int i=0;i<vpq_size;i++){
		        temph = temph+i;
			if (temph==vpq_size){
			    temph=0;
			}
			if (temph==vpq.t){
			   break;
			}

			if (active_list.at[index].pc == vpq.vpq_data[temph].pc){
			   svp_instance++;
			
			}
		   
		   }
		   svp[svp_index].instance=svp_instance;

             
       }

       vpq.h++;
       if(vpq.h == vpq.t)
    {
        vpq.h = 0;
        vpq.h_phase = !vpq.h_phase;
    }

    
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

bool renamer::stall_vpq(uint64_t bundle_vp_eligible){

uint64_t vpq_count;
    if(vpq.h_phase == vpq.t_phase)
    {
        vpq_count =vpq.t - vpq.h;
    }
    else
    {
        vpq_count = vpq_size - (vpq.h - vpq.t);
    }
    
    if(vpq_count >= bundle_vp_eligible)
    {
        return false;
    }
    else
    {
        return true;
    }


}

uint64_t renamer::vpq_update(uint64_t pc){

uint64_t index = vpq.t;
    vpq.vpq_data[index].pc = pc;
    
    vpq.t++;
    if(vpq.t == vpq_size)
    {
        vpq.t = 0;
        vpq.t_phase = !vpq.t_phase;
    }
    return index;

}
bool renamer::check_svp (uint64_t pc){

      int index = (pc >> 2) & ((1ULL << (svp_index)) - 1);
      int tag =  (pc >> svp_index) & ((1ULL << (svp_tag)) - 1);
      if (svp[index].valid && svp[index].tag==tag){
	     svp[svp_index].instance++; 
          return 1;
      
      }else{
      
      return 0;
      
      }
}

int renamer::get_svp_index(uint64_t pc){
      return (pc >> 2) & ((1ULL << (svp_index)) - 1);
}

bool renamer::is_vp_perfect(){
    return vp_perfect;
}

bool renamer::is_vp_oracle(){
    return vp_oracle;

}

int renamer::get_prediction_value(int index){


return svp[index].last_value + svp[index].stride*svp[index].instance;

}
void renamer::vp_active_list_update(int AL_index,int vp_eligible, int vp_conf){

        active_list.at[AL_index].vp_eligible = vp_eligible;
	active_list.at[AL_index].vp_conf =  vp_conf;
	
}

int renamer::get_vp_conf(){
    
	return vp_conf;

}
void renamer::set_vpq_value(int index,uint64_t value){

	vpq.vpq_data[index].value=value;

}






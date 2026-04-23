#include "renamer.h"
#include <cassert>
#include <cstdio>
#include <cmath>  
////////////////////////////////// CONSTRUCTOR ////////////////////////////////

renamer::renamer(uint64_t n_log_regs, uint64_t n_phys_regs, uint64_t n_branches, uint64_t n_active,bool vp_perf,int vpq_size,bool vp_oracle_conf,int svp_index_bits,int svp_tag_bits,int vp_confmax,int vp_eligible_intalu,int vp_eligible_fpalu,int vp_eligible_load,bool lvp_en, int lvp_index_bits, int lvp_tag_bits, int lvp_confmax,bool fcm_en,int fcm_pred_index_bits, int fcm_pred_tag_bits,int fcm_ctx_index_bits,  int fcm_ctx_tag_bits,int fcm_confmax,bool gshare_en,int gshare_idx_bits_p, int gshare_tag_bits_p,int gshare_confmax, int gshare_history_bits_p)
{
    logical_reg_count = n_log_regs;
    physical_reg_count = n_phys_regs;
    unresolved_branch_count = n_branches;
    active_list_size = n_active;

    // LVP initialization
    lvp_enabled = lvp_en;
    lvp_index   = lvp_index_bits;
    lvp_tag     = lvp_tag_bits;
    lvp_conf_max = lvp_confmax;
    
    if (lvp_enabled) {
        lvp = new lvp_struct[1 << lvp_index_bits];
        for (int i = 0; i < (1 << lvp_index_bits); i++) {
            lvp[i].valid = 0;
            lvp[i].tag = 0;
            lvp[i].last_value = 0;
            lvp[i].conf = 0;
        }
    } else {
        lvp = nullptr;
    }

    fcm_enabled     = fcm_en;
    fcm_pred_index  = fcm_pred_index_bits;
    fcm_pred_tag    = fcm_pred_tag_bits;
    fcm_ctx_index   = fcm_ctx_index_bits;
    fcm_ctx_tag     = fcm_ctx_tag_bits;
    fcm_conf_max    = fcm_confmax;
    
    if (fcm_enabled) {
        fcm_pred = new fcm1_entry_t[1 << fcm_pred_index_bits];
        for (int i = 0; i < (1 << fcm_pred_index_bits); i++) {
            fcm_pred[i].valid = 0;
            fcm_pred[i].tag = 0;
            fcm_pred[i].next_value = 0;
            fcm_pred[i].conf = 0;
        }
    
        fcm_ctx = new fcm1_ctx_entry_t[1 << fcm_ctx_index_bits];
        for (int i = 0; i < (1 << fcm_ctx_index_bits); i++) {
            fcm_ctx[i].valid = 0;
            fcm_ctx[i].tag = 0;
            fcm_ctx[i].prev_value = 0;
        }
    } else {
        fcm_pred = nullptr;
        fcm_ctx  = nullptr;
    }

    // gshare-VP initialization
     gshare_enabled       = gshare_en;
     gshare_idx_bits      = gshare_idx_bits_p;
     gshare_tag_bits      = gshare_tag_bits_p;
     gshare_conf_max      = gshare_confmax;
     gshare_history_bits  = gshare_history_bits_p;
     committed_ghr        = 0;
     
     if (gshare_enabled) {
         gshare_vp = new gshare_vp_entry_t[1 << gshare_idx_bits];
         for (int i = 0; i < (1 << gshare_idx_bits); i++) {
             gshare_vp[i].valid = 0;
             gshare_vp[i].tag = 0;
             gshare_vp[i].value = 0;
             gshare_vp[i].conf = 0;
         }
     } else {
         gshare_vp = nullptr;
     }
    //////////////////////////////////////////
    // Value Prediction
    /////////////////////////////////////////
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
     
    for (int i=0;i<1<<svp_index_bits;i++){
       svp[i].valid=0;
	svp[i].tag=0;
	svp[i].conf=0;
	svp[i].last_value=0;
	svp[i].stride=0;
	svp[i].s1=0;
	svp[i].instance=0;
    
    }
    for(int i=0;i<vpq_size;i++){
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

void renamer::increment_svp_instance(uint64_t pc) {
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

        while (temp != vpq.t || temp_phase != vpq.t_phase) {
            uint64_t pc = vpq.vpq_data[temp].pc;
            uint64_t s_index = (pc >> 2) & ((1ULL << svp_index) - 1);
            uint64_t s_tag = (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);
            
            if (check_svp(pc)) {
                if (svp[s_index].instance > 0) {
                    svp[s_index].instance--;
                }
            }
            
            temp++;
            if (temp == (uint64_t)vpq_size) {
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
    
    if (active_list.at[index].vp_eligible){
    vp_eligible_count++;
    if (active_list.at[index].vp_no_pred){
        vp_miss++; 
    }else{
        if (active_list.at[index].vp_conf == vp_conf){
            vp_conf_corr++;  // Count ALL confident predictions
            if (!active_list.at[index].vp_pred_correct){
                vp_conf_incorr++;  // Also count incorrect ones separately
            }
        }else{
            if (active_list.at[index].vp_pred_correct){
                vp_unconf_corr++;
            }else{
                vp_unconf_incorr++;	  
            }
        }
    }
}else{
    vp_n_eligible_count++;
}

    if (active_list.at[index].vp_eligible && !vp_perfect){
       int vpq_index = vpq.h;
       bool is_load = active_list.at[index].load_flag && !active_list.at[index].amo_flag;
       bool is_alu    = !active_list.at[index].load_flag && !active_list.at[index].store_flag
                        && !active_list.at[index].branch_flag
                        && !active_list.at[index].amo_flag
                        && !active_list.at[index].csr_flag;
// is_alu covers both INT ALU and FP ALU — you can't distinguish here.
       if (is_alu || is_load ){
       uint64_t s_index = (active_list.at[index].pc >> 2) & ((1ULL << svp_index) - 1); 
       uint64_t s_tag = (active_list.at[index].pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1); 

       if (check_svp(active_list.at[index].pc)){
            int64_t new_stride = (int64_t)vpq.vpq_data[vpq_index].value - (int64_t)svp[s_index].last_value;
	    if (new_stride == svp[s_index].stride){
	      svp[s_index].conf++;
	      if (svp[s_index].conf>=vp_conf){
	          svp[s_index].conf=vp_conf;
	      }
	    
	    }//else if (new_stride == svp[s_index].s1) {
          // Tentative stride matched a second time — promote s1 to s2
               // svp[s_index].stride = svp[s_index].s1;
               // svp[s_index].conf = 0;
         //  }   
	    else{
	       svp[s_index].stride=new_stride;
	       svp[s_index].conf=0;
	  //     if (svp[s_index].conf > 0) {
	  //        svp[s_index].conf--;
	  //    }
	    }
	    //svp[s_index].s1 = new_stride;
           svp[s_index].last_value=vpq.vpq_data[vpq_index].value;
	   svp[s_index].instance--;

       
       }else{
	           int svp_instance=0;
		   svp[s_index].valid=1;
		   svp[s_index].conf=0;
		   // svp[s_index].stride=vpq.vpq_data[vpq_index].value;
		   svp[s_index].stride=0;                        
                   svp[s_index].s1=0; 
		   svp[s_index].last_value=vpq.vpq_data[vpq_index].value;
		   svp[s_index].tag = s_tag;
		   int temph = vpq.h;
		   for (int i=1;i<vpq_size;i++){
		        temph = (vpq.h+i)%vpq_size;
			//if (temph==vpq_size){
			  //  temph=0;
			//}
			if (temph==vpq.t){
			   break;
			}

			if (active_list.at[index].pc == vpq.vpq_data[temph].pc){
			   svp_instance++;
			
			}
		   
		   }
		   svp[s_index].instance=svp_instance;

             
       }
       }
       vpq.h++;
       if(vpq.h == vpq_size)
    {
        vpq.h = 0;
        vpq.h_phase = !vpq.h_phase;
    }


    if (lvp_enabled) {
    train_lvp(active_list.at[index].pc, vpq.vpq_data[vpq_index].value);
     }

    if (fcm_enabled) {
    train_fcm(active_list.at[index].pc, vpq.vpq_data[vpq_index].value);
    }
    if (gshare_enabled) {
    train_gshare(active_list.at[index].pc,
                 vpq.vpq_data[vpq_index].ghr_snapshot,
                 vpq.vpq_data[vpq_index].value);
    }

    }
    // Update committed_ghr for every retiring branch
    if (active_list.at[index].branch_flag && gshare_enabled) {
        bool actual_taken = active_list.at[index].branch_predicted_taken
                            ^ active_list.at[index].branch_mispred_flag;
        update_committed_ghr(actual_taken);
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
     
  //  int temp=vpq.h;
  //  int temp_pc=0;
  //  int temp_index=0;

  //  for (int i=0;i<vpq_size;i++){
  //   temph = (vpq.h+i)%vpq_size;
  //   temp_pc=vpq.vpq_data[temp].pc;
  //   temp_index=get_svp_index(temp_pc);
  //   if (check_svp(temp_pc)){
  //       svp[temp_index].instance--;
  //   }
  //   
  //       if (temph == vpq.t){	 
  //		 break;
  //       } 
  //  }
  uint64_t temp = vpq.h;
    bool temp_phase = vpq.h_phase;

    while (temp != vpq.t || temp_phase != vpq.t_phase) {
        uint64_t pc = vpq.vpq_data[temp].pc;
        uint64_t s_index = (pc >> 2) & ((1ULL << svp_index) - 1);
        uint64_t s_tag = (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);
        
        if (check_svp(pc)) {
            if (svp[s_index].instance > 0) {
                svp[s_index].instance--;
            }
        }
        
        temp++;
        if (temp == (uint64_t)vpq_size) {
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

bool renamer::stall_vpq(uint64_t bundle_vp_eligible){

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

uint64_t renamer::vpq_update(uint64_t pc){

uint64_t index = vpq.t;
    vpq.vpq_data[index].pc = pc;
    vpq.vpq_data[index].ghr_snapshot = committed_ghr; 
    
    vpq.t++;
    if(vpq.t == vpq_size)
    {
        vpq.t = 0;
        vpq.t_phase = !vpq.t_phase;
    }
    return index;

}
bool renamer::check_svp (uint64_t pc){
        
	if (svp_tag==0){
	return 1;
	}
      uint64_t index = (pc >> 2) & ((1ULL << svp_index) - 1);;
      uint64_t tag =  (pc >> (svp_index + 2)) & ((1ULL << svp_tag) - 1);;
      if (svp[index].valid && (svp[index].tag==tag || svp_tag==0)){
          return 1;
      
      }else{
      
      return 0;
      
      }
}

uint64_t renamer::get_svp_index(uint64_t pc){
      return (pc >> 2) & ((1ULL << svp_index) - 1);;
}

bool renamer::is_vp_perfect(){
    return vp_perfect;
}

bool renamer::is_vp_oracle(){
    return vp_oracle;

}

uint64_t renamer::get_prediction_value(uint64_t index){


return (uint64_t)((int64_t)svp[index].last_value + svp[index].stride*svp[index].instance);

}
void renamer::vp_active_list_update(uint64_t AL_index,int vp_eligible, int vp_conf,int vp_pred){

        active_list.at[AL_index].vp_eligible = vp_eligible;
	active_list.at[AL_index].vp_conf =  vp_conf;
        active_list.at[AL_index].vp_no_pred = (vp_pred==0); 
	
}
void renamer::vp_active_list_pred_no_correct(uint64_t AL_index){
       active_list.at[AL_index].vp_pred_correct=0;
}



int renamer::get_vp_conf(){
    
	return vp_conf;

}
void renamer::set_vpq_value(uint64_t index,uint64_t value){

	vpq.vpq_data[index].value=value;

}
int renamer::get_svp_conf(uint64_t index){

	return svp[index].conf;

}	

void renamer::dump_stats(FILE *fp){

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

    
    if (!vp_perfect){
    fprintf(fp, "VALUE PREDICTOR = stride (Project 4 spec. implementation)\n");
    fprintf(fp, "   VPQsize         = %d\n", vpq_size);
    fprintf(fp, "   oracleconf      = %d (%s)\n", vp_oracle, vp_oracle ? "oracle confidence" : "real confidence");
    fprintf(fp, "   # index bits    = %d\n", svp_index);
    fprintf(fp, "   # tag bits      = %d\n", svp_tag);
    fprintf(fp, "   confmax         = %d\n", vp_conf);
    }else{
    
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
    fprintf(fp, "   Total storage cost (bits) = (%lu SVP entries x %lu bits/SVP entry) = %lu bits\n", 
            svp_entries, bits_per_entry, total_bits);
    fprintf(fp, "   Total storage cost (bytes) = %.2f B (%.2f KB)\n", total_bytes, total_kb);
    }else{
    
         fprintf(fp, "  Impossible.\n");
    }

} 


bool renamer::is_lvp_enabled() {
    return lvp_enabled;
}

uint64_t renamer::get_lvp_index(uint64_t pc) {
    return (pc >> 2) & ((1ULL << lvp_index) - 1);
}

bool renamer::check_lvp(uint64_t pc) {
    if (!lvp_enabled) return false;

    uint64_t idx = get_lvp_index(pc);
    if (!lvp[idx].valid) return false;

    if (lvp_tag > 0) {
        uint64_t tag = (pc >> (lvp_index + 2)) & ((1ULL << lvp_tag) - 1);
        if (lvp[idx].tag != tag) return false;
    }
    return true;
}

uint64_t renamer::get_lvp_prediction(uint64_t pc) {
    uint64_t idx = get_lvp_index(pc);
    return lvp[idx].last_value;
}

bool renamer::lvp_hit_confidence(uint64_t pc) {
    if (!check_lvp(pc)) return false;
    uint64_t idx = get_lvp_index(pc);
    return (lvp[idx].conf == (uint64_t)lvp_conf_max);
}

void renamer::train_lvp(uint64_t pc, uint64_t value) {
    if (!lvp_enabled) return;

    uint64_t idx = get_lvp_index(pc);
    uint64_t tag = (lvp_tag > 0) ? ((pc >> (lvp_index + 2)) & ((1ULL << lvp_tag) - 1)) : 0;

    if (lvp[idx].valid && (lvp_tag == 0 || lvp[idx].tag == tag)) {
        if (lvp[idx].last_value == value) {
            // Correct — bump confidence
            if (lvp[idx].conf < (uint64_t)lvp_conf_max) {
                lvp[idx].conf++;
            }
        } else {
            // Incorrect — decrement, only replace value when conf hits zero
            if (lvp[idx].conf > 0) {
                lvp[idx].conf--;
            } else {
                lvp[idx].last_value = value;
            }
        }
    } else {
        // Miss: install
        lvp[idx].valid = 1;
        lvp[idx].tag = tag;
        lvp[idx].last_value = value;
        lvp[idx].conf = 0;
    }
}
/////////////////////////////////////////////////////////////////////////////
// Context table index: PC bits only
uint64_t renamer::fcm_ctx_idx_hash(uint64_t pc, int idx_bits) {
    return (pc >> 2) & ((1ULL << idx_bits) - 1);
}

// Context table tag: upper PC bits
uint64_t renamer::fcm_ctx_tag_hash(uint64_t pc, int idx_bits, int tag_bits) {
    if (tag_bits == 0) return 0;
    return (pc >> (idx_bits + 2)) & ((1ULL << tag_bits) - 1);
}

// Prediction table index: hash of PC and prev_value
uint64_t renamer::fcm_pred_idx_hash(uint64_t pc, uint64_t prev_value, int idx_bits) {
    uint64_t pc_bits = (pc >> 2);
    uint64_t val_fold = prev_value ^ (prev_value >> 16) ^ (prev_value >> 32) ^ (prev_value >> 48);
    return (pc_bits ^ val_fold) & ((1ULL << idx_bits) - 1);
}

// Prediction table tag: different fold to decorrelate from index
uint64_t renamer::fcm_pred_tag_hash(uint64_t pc, uint64_t prev_value, int idx_bits, int tag_bits) {
    if (tag_bits == 0) return 0;
    uint64_t pc_shift = (pc >> (idx_bits + 2));
    uint64_t val_fold = prev_value ^ (prev_value >> tag_bits) ^ (prev_value >> (2 * tag_bits));
    return (pc_shift ^ val_fold) & ((1ULL << tag_bits) - 1);
}

bool renamer::is_fcm_enabled() {
    return fcm_enabled;
}

bool renamer::check_fcm(uint64_t pc) {
    if (!fcm_enabled) return false;

    // Check context table first
    uint64_t cidx = fcm_ctx_idx_hash(pc, fcm_ctx_index);
    if (!fcm_ctx[cidx].valid) return false;
    if (fcm_ctx_tag > 0) {
        uint64_t ctag = fcm_ctx_tag_hash(pc, fcm_ctx_index, fcm_ctx_tag);
        if (fcm_ctx[cidx].tag != ctag) return false;
    }

    // Use prev_value to look up prediction table
    uint64_t prev_val = fcm_ctx[cidx].prev_value;
    uint64_t pidx = fcm_pred_idx_hash(pc, prev_val, fcm_pred_index);

    if (!fcm_pred[pidx].valid) return false;
    if (fcm_pred_tag > 0) {
        uint64_t ptag = fcm_pred_tag_hash(pc, prev_val, fcm_pred_index, fcm_pred_tag);
        if (fcm_pred[pidx].tag != ptag) return false;
    }
    return true;
}

uint64_t renamer::get_fcm_prediction(uint64_t pc) {
    uint64_t cidx = fcm_ctx_idx_hash(pc, fcm_ctx_index);
    uint64_t prev_val = fcm_ctx[cidx].prev_value;
    uint64_t pidx = fcm_pred_idx_hash(pc, prev_val, fcm_pred_index);
    return fcm_pred[pidx].next_value;
}

bool renamer::fcm_hit_confidence(uint64_t pc) {
    if (!check_fcm(pc)) return false;
    uint64_t cidx = fcm_ctx_idx_hash(pc, fcm_ctx_index);
    uint64_t prev_val = fcm_ctx[cidx].prev_value;
    uint64_t pidx = fcm_pred_idx_hash(pc, prev_val, fcm_pred_index);
    return (fcm_pred[pidx].conf == (uint8_t)fcm_conf_max);
}
void renamer::train_fcm(uint64_t pc, uint64_t value) {
    if (!fcm_enabled) return;

    uint64_t cidx = fcm_ctx_idx_hash(pc, fcm_ctx_index);
    uint64_t ctag = fcm_ctx_tag_hash(pc, fcm_ctx_index, fcm_ctx_tag);

    bool has_ctx = fcm_ctx[cidx].valid &&
                   (fcm_ctx_tag == 0 || fcm_ctx[cidx].tag == ctag);

    if (!has_ctx) {
        fcm_ctx[cidx].valid = 1;
        fcm_ctx[cidx].tag = ctag;
        fcm_ctx[cidx].prev_value = value;
        return;
    }

    uint64_t prev_val = fcm_ctx[cidx].prev_value;
    uint64_t pidx = fcm_pred_idx_hash(pc, prev_val, fcm_pred_index);
    uint64_t ptag = fcm_pred_tag_hash(pc, prev_val, fcm_pred_index, fcm_pred_tag);

    if (fcm_pred[pidx].valid &&
        (fcm_pred_tag == 0 || fcm_pred[pidx].tag == ptag)) {
        if (fcm_pred[pidx].next_value == value) {
            // Correct — bump confidence
            if (fcm_pred[pidx].conf < (uint8_t)fcm_conf_max) {
                fcm_pred[pidx].conf++;
            }
        } else {
            // Incorrect — decrement, only replace value when conf hits zero
            if (fcm_pred[pidx].conf > 0) {
                fcm_pred[pidx].conf--;
            } else {
                fcm_pred[pidx].next_value = value;
            }
        }
    } else {
        fcm_pred[pidx].valid = 1;
        fcm_pred[pidx].tag = ptag;
        fcm_pred[pidx].next_value = value;
        fcm_pred[pidx].conf = 0;
    }

    // Advance context
    fcm_ctx[cidx].prev_value = value;
}


static inline uint64_t gshare_idx_hash_fn(uint64_t pc, uint64_t ghr, int idx_bits, int hist_bits) {
    uint64_t masked_ghr = ghr & ((1ULL << hist_bits) - 1);
    // Fold GHR down to idx_bits width
    uint64_t folded = masked_ghr;
    for (int shift = idx_bits; shift < hist_bits; shift += idx_bits) {
        folded ^= (masked_ghr >> shift);
    }
    return ((pc >> 2) ^ folded) & ((1ULL << idx_bits) - 1);
}

static inline uint64_t gshare_tag_hash_fn(uint64_t pc, uint64_t ghr, int idx_bits, int tag_bits, int hist_bits) {
    if (tag_bits == 0) return 0;
    uint64_t masked_ghr = ghr & ((1ULL << hist_bits) - 1);
    uint64_t fold = masked_ghr ^ (masked_ghr >> tag_bits) ^ (masked_ghr >> (2 * tag_bits));
    return (((pc >> 2) >> idx_bits) ^ fold) & ((1ULL << tag_bits) - 1);
}

bool renamer::is_gshare_enabled() {
    return gshare_enabled;
}

uint64_t renamer::get_committed_ghr() {
    return committed_ghr;
}

void renamer::update_committed_ghr(bool taken) {
    committed_ghr = ((committed_ghr << 1) | (taken ? 1 : 0))
                    & ((1ULL << gshare_history_bits) - 1);
}

bool renamer::gshare_hit_confidence(uint64_t pc, uint64_t ghr) {
    if (!gshare_enabled) return false;
    uint64_t idx = gshare_idx_hash_fn(pc, ghr, gshare_idx_bits, gshare_history_bits);
    if (!gshare_vp[idx].valid) return false;
    if (gshare_tag_bits > 0) {
        uint64_t tag = gshare_tag_hash_fn(pc, ghr, gshare_idx_bits, gshare_tag_bits, gshare_history_bits);
        if (gshare_vp[idx].tag != tag) return false;
    }
    return (gshare_vp[idx].conf == (uint8_t)gshare_conf_max);
}

uint64_t renamer::get_gshare_prediction(uint64_t pc, uint64_t ghr) {
    uint64_t idx = gshare_idx_hash_fn(pc, ghr, gshare_idx_bits, gshare_history_bits);
    return gshare_vp[idx].value;
}

void renamer::train_gshare(uint64_t pc, uint64_t ghr, uint64_t value) {
    if (!gshare_enabled) return;
    uint64_t idx = gshare_idx_hash_fn(pc, ghr, gshare_idx_bits, gshare_history_bits);
    uint64_t tag = gshare_tag_hash_fn(pc, ghr, gshare_idx_bits, gshare_tag_bits, gshare_history_bits);

    if (gshare_vp[idx].valid && (gshare_tag_bits == 0 || gshare_vp[idx].tag == tag)) {
        if (gshare_vp[idx].value == value) {
            if (gshare_vp[idx].conf < (uint8_t)gshare_conf_max) {
                gshare_vp[idx].conf++;
            }
        } else {
            if (gshare_vp[idx].conf > 0) {
                gshare_vp[idx].conf--;
            } else {
                gshare_vp[idx].value = value;
            }
        }
    } else {
        gshare_vp[idx].valid = 1;
        gshare_vp[idx].tag = tag;
        gshare_vp[idx].value = value;
        gshare_vp[idx].conf = 0;
    }
}

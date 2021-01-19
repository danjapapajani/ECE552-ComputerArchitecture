
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         16

#define RESERV_INT_SIZE    5
#define RESERV_FP_SIZE     3
#define FU_INT_SIZE        3
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     5
#define FU_FP_LATENCY      7

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP) 

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
static int fetch_index = 0;

/* ECE552: Assignment 3 BEGIN CODE */
static int available_index = 0;
static int oldest_instr_index = 0;

/* ECE552: Assignment 3 END CODE */

/* FUNCTIONAL UNITS */

/* RESERVATION STATIONS */

 /* ECE552: Assignment 3 BEGIN CODE */
void addToInstrQ(instruction_t* instr)
{
  available_index = (oldest_instr_index + instr_queue_size) % INSTR_QUEUE_SIZE;
  instr_queue[available_index] = instr;
  instr_queue_size++;
}

void removeFromInstrQ()
{
  instr_queue[oldest_instr_index] = NULL;
  oldest_instr_index = (oldest_instr_index + 1) % INSTR_QUEUE_SIZE;
  instr_queue_size--;
}
 /* ECE552: Assignment 3 END CODE */

/* 
 * Description: 
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: Assignment 3 BEGIN CODE */
  if(instr_queue_size != 0)
    return false;

  if(fetch_index <= sim_insn)
    return false;

  for(int i = 0; i < RESERV_INT_SIZE; i++)
  {
    if(reservINT[i] != NULL)
      return false;
  }

  for(int i = 0; i < RESERV_FP_SIZE; i++)
  {
    if(reservFP[i] != NULL)
      return false;
  }

  for(int i = 0; i < FU_INT_SIZE; i++)
  {
    if(fuINT[i] != NULL)
      return false;
  }

  if(fuFP[0] != NULL)
    return false;

  /* ECE552: Assignment 3 END CODE */

  return true; //ECE552: you can change this as needed; we've added this so the code provided to you compiles
}

/* 
 * Description: 
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: Assignment 3 BEGIN CODE */

  if(commonDataBus != NULL)
  {
    //update Q values in RS and MT to NULL if a match exists
    for(int i = 0; i < RESERV_INT_SIZE; i++)
    {
      if(reservINT[i] != NULL)
      {
        for(int j = 0; j < 3; j++)
        {
          if(reservINT[i]->Q[j] == commonDataBus)
            reservINT[i]->Q[j] = NULL;
        }
      }
    }

    for(int i = 0; i < RESERV_FP_SIZE; i++)
    {
      if(reservFP[i] != NULL)
      {
        for(int j = 0; j < 3; j++)
        {
          if(reservFP[i]->Q[j] == commonDataBus)
            reservFP[i]->Q[j] = NULL;
        }
      }
    }

    for(int i = 0; i < MD_TOTAL_REGS; i++)
    {
      if(map_table[i] == commonDataBus)
        map_table[i] = NULL;
    }
  }

  commonDataBus = NULL;

  /* ECE552: Assignment 3 END CODE */

}


/* 
 * Description: 
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: Assignment 3 BEGIN CODE */

  //4 is max instr that are able to be finished at a time
  instruction_t* finish_execute[4] = {NULL};

  int finish_index = 0;
  
  //go through all functional units and check to see if an instr is finished execution
  for(int i = 0; i < FU_INT_SIZE; i++)
  {
    if(fuINT[i] != NULL)
    {
      //if finished execution this cycle
      if(current_cycle  >= (fuINT[i]->tom_execute_cycle + FU_INT_LATENCY))
      {
        finish_execute[finish_index] = fuINT[i];
        finish_index++;
      }
    }
  }

  //if FP finished execute in current cycle, place it in free spot in finish_execute
  if(fuFP[0] != NULL)
  {
    if(current_cycle >= (fuFP[0]->tom_execute_cycle + FU_FP_LATENCY))
    {
      for(int i = 0; i < 4; i++)
      {
        if(finish_execute[i] == NULL)
        {
          finish_execute[i] = fuFP[0];
          break;
        }
      }
    }
  }

  //bubble sort execution queue from oldest to youngest instr
  for(int i = 0; i < 3; i++)
  {
    for(int j = 0; j < 3 - i; j++)
    {
      if(finish_execute[j] != NULL && finish_execute[j + 1] != NULL)
      {
        if(finish_execute[j]->index > finish_execute[j + 1]->index)
        {
          instruction_t* temp = finish_execute[j];
          finish_execute[j] = finish_execute[j + 1];
          finish_execute[j + 1] = temp;
        }
      }
    }
  }

  bool found_oldest = false;

  //loop through instr that have finished executing find oldest instr and take out stores
  for(int i = 0; i < 4; i++)
  {
    if(finish_execute[i] != NULL)
    {
      if(IS_STORE(finish_execute[i]->op))
      {
        //clear out RS entry
        for(int j = 0; j < RESERV_INT_SIZE; j++)
        {
          if(reservINT[j] != NULL && (reservINT[j]->index == finish_execute[i]->index))
            reservINT[j] = NULL;
        }

        //clear out FU entry
        for(int j = 0; j < FU_INT_SIZE; j++)
        {
          if(fuINT[j] != NULL && (fuINT[j]->index == finish_execute[i]->index))
            fuINT[j] = NULL;
        }
      }
      else if(!found_oldest && commonDataBus == NULL)
      {
        found_oldest = true;
        
        finish_execute[i]->tom_cdb_cycle = current_cycle;
        commonDataBus = finish_execute[i];

        //clear RS entry and FU entry
        for(int j = 0; j < RESERV_INT_SIZE; j++)
        {
          if(reservINT[j] != NULL)
          {
            if(reservINT[j]->index == finish_execute[i]->index)
            reservINT[j] = NULL;
          }
        }

        for(int j = 0; j < RESERV_FP_SIZE; j++)
          if(reservFP[j] != NULL)
          {
            if(reservFP[j]->index == finish_execute[i]->index)
            reservFP[j] = NULL;
          }

        for(int j = 0; j < FU_INT_SIZE; j++)
          if(fuINT[j] != NULL)
          {
            if(fuINT[j]->index == finish_execute[i]->index)
              fuINT[j] = NULL;
          }

        if(fuFP[0] != NULL && fuFP[0]->index == finish_execute[i]->index)
          fuFP[0] = NULL;
      }
    }
  }
  /* ECE552: Assignment 3 END CODE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: Assignment 3 BEGIN CODE */
  instruction_t* ready_to_execute_INT[RESERV_INT_SIZE] = {NULL};
  instruction_t* ready_to_execute_FP[RESERV_FP_SIZE] = {NULL};

  int oldest_int_index = 0;
  int oldest_fp_index = 0;

  //check for RAW hazards to store instr ready to execute
  for(int i = 0; i < RESERV_INT_SIZE; i++)
  {
    if(reservINT[i] != NULL)
    {
      instruction_t* curr_instr = reservINT[i];
      if(curr_instr->Q[0] == NULL && curr_instr->Q[1] == NULL && curr_instr->Q[2] == NULL && curr_instr->tom_execute_cycle == 0)
      {
          ready_to_execute_INT[oldest_int_index] = reservINT[i];
          oldest_int_index++;
      }
    }
  }

  for(int i = 0; i < RESERV_FP_SIZE; i++)
  {
    if(reservFP[i] != NULL)
    {
      instruction_t* curr_instr = reservFP[i];
      if(curr_instr->Q[0] == NULL && curr_instr->Q[1] == NULL && curr_instr->Q[2] == NULL && curr_instr->tom_execute_cycle == 0)
      {
        ready_to_execute_FP[oldest_fp_index] = reservFP[i];
        oldest_fp_index++;
      }
    }
  }

  //bubble sort execution queues from oldest to youngest instr
  for(int i = 0; i < RESERV_INT_SIZE - 1; i++)
    for(int j = 0; j < RESERV_INT_SIZE - 1 - i; j++)
      if(ready_to_execute_INT[j] != NULL && ready_to_execute_INT[j + 1] != NULL)
        if(ready_to_execute_INT[j]->index > ready_to_execute_INT[j + 1]->index)
        {
          instruction_t* temp = ready_to_execute_INT[j];
          ready_to_execute_INT[j] = ready_to_execute_INT[j + 1];
          ready_to_execute_INT[j + 1] = temp;
        }

  for(int i = 0; i < RESERV_FP_SIZE - 1; i++)
    for(int j = 0; j < RESERV_FP_SIZE - 1 - i; j++)
      if(ready_to_execute_FP[j] != NULL && ready_to_execute_FP[j + 1] != NULL)
        if(ready_to_execute_FP[j]->index > ready_to_execute_FP[j + 1]->index)
        {
          instruction_t* temp = ready_to_execute_FP[j];
          ready_to_execute_FP[j] = ready_to_execute_FP[j + 1];
          ready_to_execute_FP[j + 1] = temp;
        }

  //save the index of ready to execute queues
  int oldest_index_int = 0;
  int oldest_index_fp = 0;

  //check FU availabilty
  for(int i = 0; i < FU_INT_SIZE; i++)
  {
    if(fuINT[i] == NULL && ready_to_execute_INT[oldest_index_int])
    {
      fuINT[i] = ready_to_execute_INT[oldest_index_int];
      fuINT[i]->tom_execute_cycle = current_cycle;
      oldest_index_int++;
    }
  }

  for(int i = 0; i < FU_FP_SIZE; i++)
  {
    if(fuFP[i] == NULL && ready_to_execute_FP[oldest_index_fp])
    {
      fuFP[i] = ready_to_execute_FP[oldest_index_fp];
      fuFP[i]->tom_execute_cycle = current_cycle;
      oldest_index_fp++;
    }
  }
  /* ECE552: Assignment 3 END CODE */
}

/* 
 * Description: 
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: Assignment 3 BEGIN CODE */

  if(instr_queue_size != 0)
  {
    if(IS_COND_CTRL(instr_queue[oldest_instr_index]->op) || IS_UNCOND_CTRL(instr_queue[oldest_instr_index]->op))
      removeFromInstrQ();
    else if(USES_INT_FU(instr_queue[oldest_instr_index]->op))
    {
      //go through all RS to see if there is available entry
      for(int i = 0; i < RESERV_INT_SIZE; i++)
      {
        //entry found
        if(reservINT[i] == NULL)
        {
          //update issue cycle and allocate RS entry for instr
          instr_queue[oldest_instr_index]->tom_issue_cycle = current_cycle;
          reservINT[i] = instr_queue[oldest_instr_index];

          //check if map table values for src operands contain a tag and update
          for(int j = 0; j < 3; j++)
            if(reservINT[i]->r_in[j] != DNA)
              if(map_table[reservINT[i]->r_in[j]] != NULL)
                reservINT[i]->Q[j] = map_table[reservINT[i]->r_in[j]];

          //update tag of result register in the map table w/ RS entry
          for(int j = 0; j < 2; j++)
            if(reservINT[i]->r_out[j] != DNA)
              map_table[reservINT[i]->r_out[j]] = reservINT[i];
        
          removeFromInstrQ();
          break;
        }
      }
    }
    else if(USES_FP_FU(instr_queue[oldest_instr_index]->op))
    {
      //go through all RS to see if there is available entry
      for(int i = 0; i < RESERV_FP_SIZE; i++)
      {
        //entry found
        if(reservFP[i] == NULL)
        {
          //update issue cycle and allocate RS entry for instr
          instr_queue[oldest_instr_index]->tom_issue_cycle = current_cycle;
          reservFP[i] = instr_queue[oldest_instr_index];

          //check if map table values for src operands contain a tag and update
          for(int j = 0; j < 3; j++)
            if(reservFP[i]->r_in[j] != DNA)
              if(map_table[reservFP[i]->r_in[j]] != NULL)
                reservFP[i]->Q[j] = map_table[reservFP[i]->r_in[j]];

          //update tag of result register in the map table w/ RS entry
          for(int j = 0; j < 2; j++)
            if(reservFP[i]->r_out[j] != DNA)
              map_table[reservFP[i]->r_out[j]] = reservFP[i];

          removeFromInstrQ();
          break;
        }
      }
    } 
  }
  /* ECE552: Assignment 3 END CODE */ 
}

/* 
 * Description: 
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: Assignment 3 BEGIN CODE */

  //if intr_queue isn't full, we can grab next instr
  if(instr_queue_size < INSTR_QUEUE_SIZE)
  {
    fetch_index++;

    if(fetch_index <= sim_num_insn)
    {
      while(IS_TRAP(get_instr(trace, fetch_index)->op))
        fetch_index++;

      instruction_t* instr = get_instr(trace, fetch_index);
      addToInstrQ(instr);
    }
  }

   /* ECE552: Assignment 3 END CODE */
}

/* 
 * Description: 
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);

  /* ECE552: Assignment 3 BEGIN CODE */

  available_index = (oldest_instr_index + instr_queue_size - 1) % INSTR_QUEUE_SIZE;
  instruction_t* youngest_instr = instr_queue[available_index];

  if(youngest_instr != NULL)
    youngest_instr->tom_dispatch_cycle = current_cycle; 
       
  /* ECE552: Assignment 3 END CODE */
}

/* 
 * Description: 
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }
  
  int cycle = 1;
  while (true) {
    
     /* ECE552: Assignment 3 BEGIN CODE */
     CDB_To_retire(cycle);
     execute_To_CDB(cycle);
     issue_To_execute(cycle);
     dispatch_To_issue(cycle);
     fetch_To_dispatch(trace, cycle);
     
     cycle++;

     if (is_simulation_done(sim_num_insn))
        break;
    /* ECE552: Assignment 3 END CODE */
  }
  
  return cycle;
}

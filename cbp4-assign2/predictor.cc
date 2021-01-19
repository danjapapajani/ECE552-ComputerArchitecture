#include "predictor.h"
#include <stdlib.h>

/////////////////////////////////////////////////////////////
// 2bitsat
/////////////////////////////////////////////////////////////
int BPB[4096]; 

void InitPredictor_2bitsat() {
  //initialize every prediction to be weak N
  for (int i =0; i < 4096; i++){
    BPB[i] = 1; //weak N
  }
}

bool GetPrediction_2bitsat(UINT32 PC) {
  //get the last 12 bits to index into the BPB
  int mask = 4095; //12 1s
  int idx = PC & mask;
  int pred = BPB[idx];
  if (pred == 0 || pred == 1){
    return NOT_TAKEN;
  }
  else {
    return TAKEN;
  }
}

void UpdatePredictor_2bitsat(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  int mask = 4095;
  int idx = PC & mask;
  int pred = BPB[idx];
  if (resolveDir == TAKEN){ //update BPB index to make the prediction lean more towards taken
    if (pred == 0){ //strongly NT
      BPB[idx] = 1; //update to weakly NT
    }
    else if (pred == 1){
      BPB[idx] = 2;
    }
    else if (pred == 2){
      BPB[idx] = 3;
    }
    else {
      BPB[idx] = 3;
    }
  }
  else { //it was NOT_TAKEN
    if (pred == 0){
      BPB[idx] = 0;
    }
    else if (pred == 1){
      BPB[idx] = 0;
    }
    else if (pred == 2){
      BPB[idx] = 1;
    }
    else {
      BPB[idx] = 2;
    }
  }
}

/////////////////////////////////////////////////////////////
// 2level
/////////////////////////////////////////////////////////////

int BHT[512];
int PHT[8][64];
void InitPredictor_2level() {
  //initialize all PHTs to weakly NT
  for (int i = 0; i < 8; i++){
    for (int j =0; j < 64; j++){
      PHT[i][j] = 1;
    }
  }

  //initialize BHT/BPB to N
  for (int i = 0; i < 512; i++){
    BHT[i] = 0;
  }
}

bool GetPrediction_2level(UINT32 PC) {
  int BHT_mask = 511; //9 1s
  int PHT_mask = 7; //3 1s
  int PHT_idx = PC & PHT_mask;
  int BHT_idx = (PC >> 3) & BHT_mask;
  int pred = PHT[PHT_idx][BHT[BHT_idx]];

  if (pred == 0 || pred == 1){
    return NOT_TAKEN;
  }
  else{
    return TAKEN;
  }

}

void UpdatePredictor_2level(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  int BHT_mask = 511;
  int PHT_mask = 7;
  int PHT_idx = PC & PHT_mask;
  int BHT_idx = (PC >> 3) & BHT_mask;
  int pred = PHT[PHT_idx][BHT[BHT_idx]];

  if (resolveDir == TAKEN){
    if (pred == 0 || pred == 1 || pred == 2){ //update to predict towards taken
      PHT[PHT_idx][BHT[BHT_idx]]++;
      BHT[BHT_idx] = (BHT[BHT_idx] << 1 | 1) & 63;  
    }
    else{
      BHT[BHT_idx] = (BHT[BHT_idx] << 1 | 1) & 63;
    }
  }
  else { //NOT TAKEN
    if (pred == 1 || pred == 2 || pred == 3){ 
      PHT[PHT_idx][BHT[BHT_idx]]--;
      BHT[BHT_idx] = (BHT[BHT_idx] << 1 | 0) & 63; 
    }
    else {
      BHT[BHT_idx] = (BHT[BHT_idx] << 1 | 0) & 63;
    }
  }
}

/////////////////////////////////////////////////////////////
// openend
/////////////////////////////////////////////////////////////
/*
    weight bits: 8 (recommendation from paper based on history length)
    history length: 36 bytes (recommendation from paper)
    num perceptrons: 400

*/

#define NUM_PERCEPTRONS 400
#define HISTORY_LENGTH 36
// 400 * 36 * 8
int perceptron_table[NUM_PERCEPTRONS][HISTORY_LENGTH];
// 36 * 8
int ghr[HISTORY_LENGTH];
int head = 0;
// given in perceptron paper as best calculation for theta
int threshold = 1.93 * HISTORY_LENGTH + 14; //theta value (for training)

void InitPredictor_openend() {

  //initial weights are 0
  for (int i = 0; i < NUM_PERCEPTRONS; i++){
    for (int j = 0; j < HISTORY_LENGTH; j++){
      perceptron_table[i][j] = 0;
    }
  }

  //initialize ghr to taken
  // 1 = taken, -1 = not taken
  for (int i = 0; i < HISTORY_LENGTH; i++){
    ghr[i] = 1;
  }

}

bool GetPrediction_openend(UINT32 PC) {
  int index = PC % NUM_PERCEPTRONS; //hash to get index into perceptron table
  int y = 0;

  //compute the dot product
  for (int i = 1; i < HISTORY_LENGTH; i++){
    int ghr_index = (i + head) % HISTORY_LENGTH;
    y = y + ghr[ghr_index] * perceptron_table[index][i]; //xi * wi
  } 
  y = y + perceptron_table[index][0]; //y = w0 + xi * wi 

  if (y < 0){
    return NOT_TAKEN;
  }
  else{
    return TAKEN;
  }
  
}

void UpdatePredictor_openend(UINT32 PC, bool resolveDir, bool predDir, UINT32 branchTarget) {
  int index = PC % NUM_PERCEPTRONS;
  int t;
  int y = 0;
  int max_num = 128; //largest number given the 8 weight bits (7 1s)

  head = head % HISTORY_LENGTH;

  for (int i = 1; i < HISTORY_LENGTH; i++){
    int ghr_index = (i + head) % HISTORY_LENGTH;
    y = y + ghr[ghr_index] * perceptron_table[index][i]; //xi * wi
  } 
  y = y + perceptron_table[index][0]; //y = w0 + xi * wi 

  if (resolveDir == TAKEN){
    t = 1;
  }
  else {
    t = -1;
  }

  // if the prediction was incorrect, fix/train the perceptron
  if ((resolveDir != predDir) || (abs(y) <= threshold)){
    for (int i = 0; i < HISTORY_LENGTH; i++){
      int ghr_index = (i + head) % HISTORY_LENGTH;
      int new_weight = perceptron_table[index][i] + t * ghr[ghr_index]; // wi = wi + t * xi
      
      if (new_weight > max_num){ //if it's greater than max, set it to the max
        perceptron_table[index][i] = max_num;
      }
      else if (new_weight < (-1 * max_num)){ //if it's less than min, set it to min
        perceptron_table[index][i] = -1 * max_num;
      }
      else{
        perceptron_table[index][i] = new_weight;
      }
    }
  }

  //write what the outcome was to the global history reg
  ghr[head] = t;
  head++;

}


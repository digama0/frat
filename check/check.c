#include<stdio.h>
#include<stdlib.h>
#include<stdint.h>
#include<stdbool.h>
#include<inttypes.h>

uint8_t opcode(uint8_t *proof, uint32_t pos) { 
  return proof[pos * 4]; 
}

uint32_t operand(uint8_t *proof, uint32_t pos) { 
  return (proof[(pos * 4) + 1] << 16) | (proof[(pos * 4) + 2] << 8) | (proof[(pos * 4) + 3]); 
}

/*
  Opcode Table
  0 : Endmarker
  1 : Data 
  2 : Clause head 
  3 : RUP step
*/

// Given the number of a clause, return the position of
// the last literal of the clause.
uint32_t last_lit_pos(uint8_t *proof, uint32_t cla) {
  uint32_t cla_pos = operand(proof, cla);  
  return cla_pos + operand(proof, cla_pos);
}

uint32_t complement(uint32_t lit) {
  return ((lit + 0x800000) & 0xFFFFFF);
}

bool occurred(uint8_t *proof, uint32_t lit_pos, uint32_t lit) {
  if (opcode(proof, lit_pos) == 1) {
    if (lit == operand(proof, lit_pos)) { return true; }
    else { return occurred(proof, lit_pos - 1, lit); }
  }
  else { return false; }
}

// Check whether `sup` is a superclause of `sub`, where `sup` and `sub` are 
// clauses whose last literals are at `sup_pos` and `sub_pos`, respectively.
bool superclause(uint8_t *proof, uint32_t sup_pos, uint32_t sub_pos) {
  if (opcode(proof, sub_pos) == 2) { return true; }
  else {
    if (occurred(proof, sup_pos, operand(proof, sub_pos))) { 
      return superclause(proof, sup_pos, sub_pos - 1);
    }
    else { return false; }
  }
}

bool check_rup(uint8_t *proof, uint32_t lit_pos, uint32_t step) {
  switch (opcode(proof, lit_pos)) {
    // If all the literals have been processed, this indicates
    // that the last literal added was complementary to a 
    // prexisting literal. Check that this is in fact the case.
    case 0 : {
      uint32_t last_lit = operand(proof, lit_pos - 1);
      return occurred(proof, lit_pos - 2, complement(last_lit));
    }
    // If lit_pos points to a literal, this is a new literal to be
    // obtained by unit propagation.
    case 1 : {
      uint32_t src_lit_pos = last_lit_pos(proof, operand(proof, step));
      return superclause(proof, lit_pos, src_lit_pos);
    }
    default : 
      return false;
  }
}

bool check(uint8_t *proof, uint32_t cla, uint32_t step_pos) {
  // If all the clauses have been processed, quit with success.
  if (opcode(proof, cla) == 0) { 
    return true; 
  }
  // If `cla` points to a new clause to be added
  else {
    switch (opcode(proof, step_pos)) {
      case 3 : {
        uint32_t lit_pos = last_lit_pos(proof, cla) + 1;
        return check_rup(proof, lit_pos, step_pos);
      }
      default : 
        return false; // Currently the checker only supports RUP steps
    }
  }
}

uint32_t find_step(uint8_t *proof, uint32_t pos) {
  if (2 < opcode(proof, pos)) { return pos; }
  else { find_step(proof, pos + 1); }
} 

int main(int argc, uint8_t *argv[]) {
  uint8_t * proof = 0;
  long length;
  FILE * prooffile = fopen(argv[1], "rb");

  if(prooffile) {
    fseek(prooffile, 0, SEEK_END);
    length = ftell(prooffile);
    fseek(prooffile, 0, SEEK_SET);
    proof = malloc(length);
    if(proof) {
      fread (proof, 1, length, prooffile);
    }
    fclose (prooffile);
  }
  
  if(proof) {
    // The very first cell contains number of input clauses.
    // The checker skips this number of clauses in the beginning,
    // as these clauses need not be justified. 
    uint32_t cla = operand(proof, 0) + 1;
    // printf("%08" PRIx32 "\n", cla);

    // step is the position of the first inference step,
    // where the proof begins in earnest
    uint32_t step = find_step(proof, 0);

    if (check(proof, cla, step)) { 
      printf("Valid"); 
    }
    else { 
      printf("Invalid"); 
    }
  }
}
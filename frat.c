#include <stdio.h>
#include <stdlib.h>

#define ERROR 1
#define INIT 128
#define push_back(buffer, val) { \
  if (buffer ## Size == buffer ## Alloc) { \
    buffer ## Alloc += buffer ## Alloc >> 1; \
    buffer = (typeof(buffer)) realloc(buffer, sizeof(*buffer) * buffer ## Alloc); } \
  buffer[buffer ## Size++] = val; }
#define max(a, b) ({ int _x = a; int _y = b; _x < _y ? _y : _x; })

int* buffer = 0;
int bufferAlloc = 0;
int bufferSize = 0;

typedef struct {
  int lit;
  int step;
  int necessary;
  int* hyps;
} RUPstep;

int nSteps = 1;
RUPstep* RUPsteps = 0;
int RUPstepsSize = 0;
int RUPstepsAlloc = 0;
int* RUPbuffer = 0;
int RUPbufferSize = 0;
int RUPbufferAlloc = 0;
int* generation = 0;

void print_lit_only(int lit, int gen) {
  if (gen == 0) printf("%d", lit);
  else if (gen > 0) printf("%d.%d", lit, gen);
  else printf("%d.%d", -lit, -gen);
}
void print_lit(int lit) {
  printf(" | ");
  print_lit_only(lit, generation[abs(lit) - 1]);
}

#define RUP_UP 1
#define RUP_AT 2
int RUP(int* steps, int* formula, int formulaSize, int* clause) {
  int localSteps = 1;

  // try unit propagation
  int* units = RUPbuffer;
  for (int i = 0; i < formulaSize; i++)
    if (buffer[formula[i]] && !buffer[formula[i]+1]) push_back(RUPbuffer, i);
  push_back(RUPbuffer, -1);
  for (int i = 0; i < formulaSize; i++) {
    int hyps = RUPbufferSize;
    push_back(RUPbuffer, steps[i]);
    for (int* p = buffer + formula[i]; *p; p++) {
      int step = 0;
      for (int* u = units; *u >= 0; u++)
        if (buffer[formula[*u]] == -*p) {
          push_back(RUPbuffer, steps[*u]);
          goto foundLit;
        }
      for (int* q = clause; *q; q++) {
        if (*q == *p) goto foundLit;
      }
      goto failUP;
      foundLit:;
    }
    push_back(RUPbuffer, 0);
    push_back(RUPsteps, ((RUPstep){0, 0, 0, RUPbuffer + hyps}));
    return RUP_UP;
    failUP: RUPbufferSize = hyps;
  }

  // try reverse unit propagation (asymmetric tautology)
  for (int* p = clause; *p; p++)
    push_back(RUPsteps, ((RUPstep){-*p, -(localSteps++), 0, 0}));
  while (1) {
    int progress = 0;
    for (int i = 0; i < formulaSize; i++) {
      int lit = 0;
      int hyps = RUPbufferSize;
      int trivial = 1;
      push_back(RUPbuffer, steps[i]);
      for (int* p = buffer + formula[i]; *p; p++) {
        int step = 0;
        for (int j = 0; j < RUPstepsSize; j++)
          if (RUPsteps[j].lit == -*p) { step = RUPsteps[j].step; break; }
        if (step != 0) { trivial = 0; push_back(RUPbuffer, step); }
        else if (lit) goto failRUP;
        else lit = *p;
      }
      for (int j = 0; j < RUPstepsSize; j++)
        if (RUPsteps[j].lit == lit) goto failRUP;
      push_back(RUPbuffer, 0);
      push_back(RUPsteps, ((RUPstep){lit,
        trivial ? steps[i] : -localSteps, 0, RUPbuffer + hyps}));
      localSteps++;
      if (!lit) return RUP_AT;
      progress = 1;
      continue;
      failRUP: RUPbufferSize = hyps;
    }
    if (!progress) {
      // printf(" failed\nRUP =");
      // for (int j = 0; j < RUPstepsSize; j++) print_lit(RUPsteps[j].lit);
      // printf("\nformula:\n");
      // for (int i = 0; i < formulaSize; i++) {
      //   int taut = 0;
      //   printf("%d: ", steps[i]);
      //   for (int* p = buffer + formula[i]; *p; p++)
      //     for (int j = 0; j < RUPstepsSize; j++)
      //       if (RUPsteps[j].lit == *p) taut = 1;
      //   for (int* p = buffer + formula[i]; *p; p++) {
      //     int step = 0;
      //     for (int j = 0; j < RUPstepsSize; j++)
      //       if (RUPsteps[j].lit == -*p) goto skip;
      //     print_lit(*p);
      //     skip:;
      //   }
      //   if (taut) printf(" taut");
      //   printf("|\n");
      //   taut:;
      // }
      return 0;
    }
  }
}

int printRUP(int RUPresult, int begin, int end) {
  switch (RUPresult) {
    case RUP_UP: {
      printf("%d: UP", nSteps);
      for (int* p = RUPsteps[begin].hyps; *p; p++) printf(" %d", *p);
    } return 1;
    case RUP_AT: {
      int stack = RUPbufferSize;
      push_back(RUPbuffer, end-1);
      while (RUPbufferSize > stack) {
        RUPstep* s = RUPsteps + RUPbuffer[--RUPbufferSize];
        s->necessary = 1;
        if (s->hyps && s->hyps[1])
          for (int* p = s->hyps; *p; p++) if (*p < 0) {
            int i = begin + -*p - 1;
            if (!RUPsteps[i].necessary) push_back(RUPbuffer, i);
          }
      }
      for (int i = begin; i < end; i++) {
        RUPstep s = RUPsteps[i];
        if (s.necessary) {
          if (s.hyps) {
            printf(" .%d: UP", -s.step);
            for (int* p = s.hyps; *p; p++) {
              if (*p > 0) printf(" %d", *p);
              else printf(" .%d", -*p);
            }
            if (s.lit) print_lit(s.lit);
            printf("\n");
          } else {
            printf(" .%d: hyp", -s.step);
            print_lit(s.lit);
            printf("\n");
          }
        }
      }
      printf("%d: AT", nSteps);
    } return 1;
  }
  return 0;
}

typedef struct {
  unsigned size;
  int uses, usesEnd;
  int conjuncts, positive;
  int RUPtype;
  int RUPresults;
} RATresult;

RATresult* RATresults = 0;
int RATresultsSize = 0;
int RATresultsAlloc = 0;

RATresult* tryRAT(int* steps, int* formula, int formulaSize, int* clause, int lit) {
  push_back(RATresults, (RATresult){});
  RATresult* r = RATresults + (RATresultsSize-1);
  r->uses = RUPbufferSize;
  for (int i = 0; i < formulaSize; i++) {
    for (int* p = buffer + formula[i]; *p; p++) {
      if (*p == lit) { push_back(RUPbuffer, i); r->positive = 1; break; }
      if (*p == -lit) { push_back(RUPbuffer, ~i); r->conjuncts++; break; }
    }
  }
  r->usesEnd = RUPbufferSize;
  r->size += r->usesEnd - r->uses;

  if (r->conjuncts) {
    if (r->positive) r->size++;
    for (int u = r->uses; u < r->usesEnd; u++) if (RUPbuffer[u] < 0) {
      int i = ~RUPbuffer[u];
      for (int* p = buffer + formula[i]; *p; p++) if (*p != -lit)
        r->size++;
    }
  } else r->size++;

  if (r->conjuncts) {
    r->RUPresults = RUPbufferSize;
    for (int u = r->uses; u < r->usesEnd; u++) if (RUPbuffer[u] < 0) {
      push_back(RUPbuffer, 0);
      push_back(RUPbuffer, 0);
      push_back(RUPbuffer, 0);
    }
    int k = r->RUPresults;
    for (int u = r->uses; u < r->usesEnd; u++) if (RUPbuffer[u] < 0) {
      int i = ~RUPbuffer[u];
      RUPbuffer[k++] = RUPbufferSize;
      RUPbuffer[k++] = RUPstepsSize;
      int* resolvent = RUPbuffer + RUPbufferSize;
      for (int* p = buffer + formula[i]; *p; p++) if (*p != -lit) {
        r->size++;
        push_back(RUPbuffer, *p);
      }
      for (int* p = clause; *p; p++) if (*p != lit) {
        r->size++;
        push_back(RUPbuffer, *p);
      }
      push_back(RUPbuffer, 0);
      r->RUPtype = RUP(steps, formula, formulaSize, resolvent);
      RUPbuffer[k++] = RUPstepsSize;
      switch (r->RUPtype) {
        case RUP_UP: r->size++; break;
        case RUP_AT: r->size += RUPstepsSize - RUPbuffer[k-1]; break;
        default: r->usesEnd = u+1; return 0;
      }
    }
  }
  r->size++;
  return r;
}

int main(int argc, char** argv) {
  if (argc != 3) return 1;
  FILE* inputFile = fopen(argv[1], "r");
  if (inputFile == NULL) {
    printf("error opening \"%s\".\n", argv[1]); return ERROR; }

  int nVars     = 0;
  long nClauses = 0;

  inputLoop: switch (getc_unlocked(inputFile)) {
    case 'c': while (getc_unlocked(inputFile) != '\n'); goto inputLoop;
    case 'p': {
      if (fscanf(inputFile, " cnf %i %li \n", &nVars, &nClauses) == 2)
        break;
    } // fallthrough
    default: printf("error reading input file\n"); return ERROR;
  }
  int* formula = (int*)malloc(sizeof(int) * nClauses);
  int* steps = (int*)malloc(sizeof(int) * nClauses);

  bufferAlloc = INIT;
  buffer = (int*)malloc(sizeof(int) * bufferAlloc);
  bufferSize = 0;

  int clauseStart = 0;
  for (int clauses = 0; clauses < nClauses;) {
    int lit = 0;
    if (fscanf(inputFile, " %i ", &lit) != 1) return 2;
    push_back(buffer, lit);
    if (!lit) {
      steps[clauses] = nSteps++;
      formula[clauses++] = clauseStart;
      clauseStart = bufferSize;
    }
  }
  fclose(inputFile);

  int generationAlloc = nVars;
  generation = (int*)calloc(generationAlloc, sizeof(int));
  for (int i = 0; i < nClauses; i++) {
    printf("%d: hyp", steps[i]);
    for (int* p = buffer + formula[i]; *p; p++) print_lit(*p);
    printf("\n");
  }
  FILE* proofFile = fopen(argv[2], "r");
  if (proofFile == NULL) {
    printf("error opening \"%s\".\n", argv[2]); return ERROR; }

  int binaryMode = 0;
  { int c1 = getc_unlocked(proofFile);
    if (c1 == 'a') binaryMode = 1;
    else if (c1 == 'd') {
      int c2 = getc_unlocked(proofFile);
      binaryMode = c2 != ' '; // bad luck if you try to delete variable 32
      ungetc(c2, proofFile);
    } else binaryMode = 0;
    ungetc(c1, proofFile); }

  int formulaAlloc = nClauses;
  int formulaSize = nClauses;
  int stepsAlloc = nClauses;
  int stepsSize = nClauses;

  RUPstepsAlloc = INIT;
  RUPsteps = (RUPstep*)malloc(sizeof(RUPstep) * RUPstepsAlloc);
  RUPbufferAlloc = INIT;
  RUPbuffer = (int*)malloc(sizeof(int) * RUPbufferAlloc);
  RATresultsAlloc = INIT;
  RATresults = (RATresult*)malloc(sizeof(RATresult) * RATresultsAlloc);

  while (1) {
    int k;
    int clauseIdx = bufferSize;
    if (binaryMode) {
      if ((k = getc_unlocked(proofFile)) == EOF) break;
      int c;
      while (1) {
        unsigned int ulit = 0, mul = 0;
        do {
          c = getc_unlocked(proofFile);
          ulit |= (c & 0x7F) << mul;
          mul += 7;
        } while (c & 0x80);
        int lit = (ulit & 1) ? -(ulit >> 1) : ulit >> 1;
        push_back(buffer, lit);
        if (!lit) break;
      }
    } else {
      if (fscanf(proofFile, " "));
      k = getc_unlocked(inputFile);
      if (k == EOF) break;
      if (k != 'd') { ungetc(k, inputFile); k = 'a'; }
      int lit;
      while (1) {
        if (fscanf(proofFile, " %d", &lit) != 1) goto bigLoop;
        push_back(buffer, lit);
        if (!lit) break;
      }
    }
    int* clause = buffer + clauseIdx;

    // printf("formula:\n");
    // for (int i = 0; i < formulaSize; i++) {
    //   printf("  %d: ", steps[i]);
    //   for (int* p = buffer + formula[i]; *p; p++) print_lit(*p);
    //   printf("\n");
    // }

    // printf("--- %c", k);
    // for (int* p = clause; *p; p++) printf(" %d", *p);
    // printf("\n");

    switch (k) {
      case 'a': {
        for (int* p = clause; *p; p++) if (abs(*p) > generationAlloc) {
          printf("expand\n");
          int a = generationAlloc;
          generationAlloc = max(a + (a >> 1), abs(*p));
          generation = (int*) realloc(generation, sizeof(int) * generationAlloc);
          for (int i = a; i < generationAlloc; i++) generation[i] = 0;
        }

        RUPstepsSize = 0;
        RUPbufferSize = 0;
        int rup = RUP(steps, formula, formulaSize, clause);
        if (printRUP(rup, 0, RUPstepsSize)) {
          for (int* p = clause; *p; p++) print_lit(*p);
          printf("\n");
        } else {
          // There is a literal l in C such that
          // for each clause C' in F with ~l in C', C >< C' has AT.
          // Then F, C |- _|_ implies F |- _|_

          // Shows l|Di, ~l|C'i |- x'|Di, ~x'|C'i, x'|C
          // 1:Hyp        |- l|Di
          // 2:Hyp        |- ~l|C'i
          // 3:def        x' := l|C'
          // 1':1,3:orL   |- x'|Di
          // 4:andE       |- ~C'|C'i  <- not cnf
          // 2':3,2,4:orE |- ~x'|C'i
          // 5:AT         |- C'i|C
          // 6:5:andI     |- C'|C     <- not cnf
          // 7:3,6:orR    |- x'|C

          // 2:Hyp        |- ~l|C'i
          // 3:def        x' := C'
          // 4:andE       |- ~C'|C'i  <- not cnf
          // 2':3,4:def   |- ~x'|C'i
          // 5:AT         |- C'i|C
          // 6:5:andI     |- C'|C     <- not cnf
          // 7:3,6:def    |- x'|C

          // 3:def        x' := true
          // 1':3:trueI   |- x'|Di
          // 7:3:trueI    |- x'|C

          RATresultsSize = 0;
          RATresult* r = 0;
          int lit = 0;
          printf("attempts:");
          for (int* p = clause; *p; p++) {
            RATresult* cur = tryRAT(steps, formula, formulaSize, clause, *p);
            if (cur) printf(" %d", cur->size); else printf(" fail");
            if (cur && (!r || cur->size < r->size)) { r = cur; lit = *p; }
          }
          printf("\n");
          if (!r) { r = RATresults; lit = clause[0]; }
          int oldgen = generation[abs(lit) - 1];
          int newgen = (lit > 0) == (oldgen > 0) ? abs(oldgen)+1 : -(abs(oldgen)+1);
          int def = nSteps++;
          printf("~%d: ", def);
          print_lit_only(lit, newgen);
          printf(" := ");
          if (r->conjuncts) {
            char* startLine = "(\n    (";
            if (r->positive) {
              print_lit_only(lit, oldgen);
              startLine = " | (\n    (";
            }
            for (int u = r->uses; u < r->usesEnd; u++) if (RUPbuffer[u] < 0) {
              char* start = startLine;
              int i = ~RUPbuffer[u];
              for (int* p = buffer + formula[i]; *p; p++) if (*p != -lit) {
                printf("%s", start);
                print_lit_only(*p, generation[abs(*p) - 1]);
                start = " | ";
              }
              startLine = ")\n  & (";
            }
            printf("))\n");
          } else printf("true\n");

          generation[abs(lit) - 1] = newgen;
          for (int u = r->uses; u < r->usesEnd; u++) {
            int i;
            if (RUPbuffer[u] >= 0) { i = RUPbuffer[u];
              if (r->conjuncts)
                printf("~%d: orL %d %d", nSteps, def, steps[i]);
              else printf("~%d: trueI %d", nSteps, def);
            } else { i = ~RUPbuffer[u];
              if (r->positive)
                printf("~%d: orE_andE %d %d", nSteps, def, steps[i]);
              else printf("~%d: andE %d", nSteps, def);
            }
            for (int* p = buffer + formula[i]; *p; p++) print_lit(*p);
            printf("\n");
            steps[i] = nSteps++;
          }
          if (r->conjuncts) {
            int* rp = RUPbuffer + r->RUPresults;
            for (int u = r->uses; u < r->usesEnd; u++) if (RUPbuffer[u] < 0) {
              int i = ~RUPbuffer[u];
              int* resolvent = RUPbuffer + *rp++;
              int begin = *rp++;
              int end = *rp++;
              if (!printRUP(r->RUPtype, begin, end))
                printf("~%d: failed", nSteps);
              nSteps++;
              for (int* p = resolvent; *p; p++) print_lit(*p);
              printf("\n");
            }
            if (r->positive) printf("%d: orR_andI %d", nSteps, def);
            else printf("%d: andI %d", nSteps, def);
            int newStep = nSteps;
            nSteps -= r->conjuncts;
            while (nSteps < newStep) printf(" %d", nSteps++);
          } else printf("%d: trueI %d", nSteps, def);
          print_lit(lit);
          for (int* p = clause; *p; p++) if (*p != lit) print_lit(*p);
          printf("\n");
        }
        push_back(formula, clauseIdx);
        push_back(steps, nSteps);
        nSteps++;
      } break;
      case 'd': {
        for (int i = 0; i < formulaSize; i++) {
          int* p = buffer + formula[i], *q = clause;
          while (*p && *p == *q) {p++; q++;}
          if (*p == 0 && *q == 0) {
            printf("clear %d\n", steps[i]);
            while (++i < formulaSize) {
              formula[i-1] = formula[i];
              steps[i-1] = steps[i];
            }
            formulaSize--;
            stepsSize--;
            break;
          }
        }
      } break;
      default: printf("invalid step %d", k); return ERROR;
    }
  } bigLoop:
  fclose(proofFile);
  return 0;
}

// Simple program for reversing the order of lines in a FRAT/DRAT proof.

#include <stdio.h>
#include <stdlib.h>

#define page_size 1048576

FILE* target; 
char target_file_name[128];
char write_buffer[page_size]; 

int compute_carry(int size, char * buffer) {
  int pos = size - 1;
  while (0 < pos && buffer[pos] != 0) {pos--;}
  return page_size - (pos + 1);
}

// Requires : 0 < size
int last_bol(int size, char * buffer) {
  int pos = size - 2;
  while (0 <= pos && buffer[pos] != 0) {pos--;}
  return  pos + 1;
}

int reverse_write(int page_num, int size, char * read_buffer, char * prefix) {

  int write_pos = 0; 
  int end_mark = size; 
  int bol;

  while (0 < end_mark) {
    bol = last_bol(end_mark, read_buffer); 
    for (int read_pos = bol; read_pos < end_mark; read_pos++, write_pos++) {
      write_buffer[write_pos] = read_buffer[read_pos];
    }
    end_mark = bol;
  }

  sprintf(target_file_name, "%s%d", prefix, page_num);
  target = fopen(target_file_name, "w");
  fwrite(write_buffer, 1, write_pos, target);
  fclose(target);
}

int main(int argc, char** argv) {

  FILE* source = fopen(argv[1], "rb");
  char* target_prefix = argv[2];
  int carry_size = 0;
  int read_size = page_size; 
  char buffer[page_size]; 

  if (source) {
    for (int page_num = 0; read_size == page_size; page_num++) {
      read_size = fread(buffer + carry_size, 1, page_size - carry_size, source) + carry_size;
      carry_size = compute_carry(read_size, buffer);
      reverse_write(page_num, page_size - carry_size, buffer, target_prefix);
      for(int i = 0, j = page_size - carry_size; i < carry_size; i++, j++) {
        buffer[i] = buffer[j]; // Pull carry to beginning of buffer }
      }
    }

    fclose(source);
  }
}
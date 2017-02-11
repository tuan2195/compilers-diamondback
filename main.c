#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");

const int BOOL_TRUE  = 0xFFFFFFFF;
const int BOOL_FALSE = 0x7FFFFFFF;
const int BOOL_FLAG  = 0x1;

int print(int val)
{
    if ((val & BOOL_FLAG) == 0)
        printf("%d\n", val >> 1);
    else if (val == 0xFFFFFFFF)
        printf("true\n");
    else if (val == 0x7FFFFFFF)
        printf("false\n");
    else
        printf("Unknown value: %#010x\n", val);
    return val;
}

void error(int err)
{
    if (err == 0xA)
        printf("Error: Arithmetic operation expects a number\n");
    else if (err == 0xB)
        printf("Error: Logic/if operation expects a boolean\n");
    else if (err == 0xC)
        printf("Error: Integer overflow detected\n");
}

/*

COPY YOUR IMPLEMENTATION FROM COBRA

*/


// main should remain unchanged
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}

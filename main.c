#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int our_code_starts_here() asm("our_code_starts_here");
extern int print(int val) asm("print");
extern void error(int err) asm("error");

const int BOOL_TRUE  = 0xFFFFFFFF;
const int BOOL_FALSE = 0x7FFFFFFF;
const int BOOL_FLAG  = 0x1;

#define ERR_COMP_NOT_NUM   1
#define ERR_ARITH_NOT_NUM  2
#define ERR_LOGIC_NOT_BOOL 3
#define ERR_IF_NOT_BOOL    4
#define ERR_OVERFLOW       5

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
    if (err == ERR_COMP_NOT_NUM)
        printf("Error: Comparison operation expects a number\n");
    else if (err == ERR_ARITH_NOT_NUM)
        printf("Error: Arithmetic operation expects a number\n");
    else if (err == ERR_LOGIC_NOT_BOOL)
        printf("Error: Logic operation expects a boolean\n");
    else if (err == ERR_IF_NOT_BOOL)
        printf("Error: If operation expects a boolean\n");
    else if (err == ERR_OVERFLOW)
        printf("Error: Integer overflow detected\n");
    else
        printf("Error: Unknown error\n");
    exit(err);
}


// main should remain unchanged
int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}

/*
    nasau - virtual machine 

    nasau's current cpu opcodes are fixed length at 64 bits

    the opcodes for nasau should follow some guidelines

        1. the order of operands follows traditional writing of operations
            so the destination is always the first operand, followed by sources
            for example, add would be
                add dr, sr1, sr2
            which is equivalent to
                destination register = source register 1 + source register 2
        2. not sure of anymore yet :)

    |  ****  |
    |  bits  |
    |54    34|
     ^      ^
     |      |
     |      starting bit
     end bit 
    bits = readbits(34, 20);

---------------------------------------------------------------------------------------------------------------
nop:
  no operation

  does nothing
  
  encoding:
    normal:
        000000 | ... |
        nop    | nu  |
        63   58|57  0|
---------------------------------------------------------------------------------------------------------------
binary arithmetic:

  binary operators all follow the pattern
    dest = src1 <op> src2 
  they also set the condition flags

  opcodes:
    add  | 0b000001 | 0x01 | 1  | addition  
    sub  | 0b000010 | 0x02 | 2  | subtraction
    mul  | 0b000011 | 0x03 | 3  | multiplication
    smul | 0b000100 | 0x04 | 4  | signed multiplication 
    div  | 0b000101 | 0x05 | 5  | division
    sdiv | 0b000110 | 0x06 | 6  | signed division
    and  | 0b000111 | 0x07 | 7  | bitwise and
    or   | 0b001000 | 0x08 | 8  | bitwise or
    xor  | 0b001001 | 0x09 | 9  | bitwise xor
    shr  | 0b001010 | 0x0A | 10 | bitwise shift right
    shl  | 0b001011 | 0x0B | 11 | bitwise shift left

  encodings:
    add,sub,mul,smul,and,or,xor,shr,shl:

      if the 49th bit is 0 then the second operand is a register, if it is 1 then it is a sign extended 
      49 bit value.

      normal:
        ****** | **** | **** | 0 | **** | ... |
        opcode |  dr  |  sr1 |   |  sr2 | nu  |
        63   58|57  54|53  50| 49|48  45|44  0|

      immediate:
        ****** | **** | **** | 1 |  ...  |
        opcode |  dr  |  sr1 |   | imm49 |
        63   58|57  54|53  50| 49|48    0|

    div, sdiv:

      if the 45th bit is 0 sr1 is divided by sr2 and the quotient and remainder are stored in qr and rr respectively
      if it's 1 then sr1 is divided by imm45 and the quotient and remainder are stored in qr and rr respectively

      normal:
        ****** | **** | **** | **** | 0 | **** | ... |
        opcode |  qr  |  rr  |  sr1 |   |  sr2 | nu  |
        63   58|57  54|53  50|49  46| 45|44  41|40  0|

      immediate:
        ****** | **** | **** | **** | 1 |  ...  |
        opcode |  qr  |  rr  |  sr1 |   | imm45 |
        63   58|57  54|53  50|49  46| 45|44    0|

---------------------------------------------------------------------------------------------------------------
not:
  bitwise not

  todo desc
  
  encoding:
    normal:
      001100 | **** | **** | ... |
      not    |  dr  |  sr1 | nu  |
      63   58|57  54|53  50|49  0|

---------------------------------------------------------------------------------------------------------------
jumps:
  
  jumps move the stack pointer to a new location relative to where it was at the jump
  they can either be passed a register or an immediate value

  opcodes:
    jmp | 0b001101 | 0x0D | 13 | jumps unconditionally 
    jz  | 0b001110 | 0x0E | 14 | jumps if the last operation's result was not zero
    jnz | 0b001111 | 0x0F | 15 | jumps if the last operation's result was not zero
    jp  | 0b010000 | 0x10 | 16 | jumps if the last operation's result was positive
    jn  | 0b010001 | 0x11 | 17 | jumps if the last operation's result was negative

  encoding:
    normal:
      ****** | 0 | **** | ... |
      opcode |   |  sr1 | nu  |
      63   58| 57|56  53|52  0|
    
    immediate:
      ****** | 1 |  ...  |
      opcode |   | imm57 |
      63   58| 57|56    0|

---------------------------------------------------------------------------------------------------------------
mov:
  if 53rd bit is 0, copies data from sr1 to dr
  if 53rd bit is 1, copies data from imm53 to dr
  
  encoding:
    normal:
      010010 | **** | 0 | **** | ... |
      mov    |  dr  |   | sr1  | nu  |
      63   58|57  54| 53|52  49|48  0|

    immediate:
      010010 | **** | 1 |  ...  |
      mov    |  dr  |   | imm53 |
      63   58|57  54| 53|52    0|

---------------------------------------------------------------------------------------------------------------
memory:
  
  st and ld are used for manipulating memory connected to the cpu
  they both have a width operand which determines the size of memory to be manipulated

  widths:
    0: 8 bits
    1: 16 bits
    2: 32 bits
    3: 64 bits

  opcodes:
    st | 0b010011 | 0x13 | 19 | stores the value in sr1 at the memory location pointed to by dr
    ld | 0b010100 | 0x14 | 20 | loads the value stored at the memory location pointed to by sr1 into dr

  encoding:
    normal:
      ****** |  **   | **** | **** | ... |
      opcode | width |  dr  | sr1  | nu  |
      63   58|57   56|55  52|51  48|47  0|


*/

#ifndef NASAU_H
#define NASAU_H
#include "common.h"
extern "C"{

#define ureg(x) machine->reg[x].u
#define sreg(x) machine->reg[x].s
#define freg(x) machine->reg[x].f
#define readbits(start, numbits) ReadBits64(instr, start, numbits)

struct Reg{
    union{
        u64 u;
        s64 s;
        f64 f;
    };
};
    
enum{
    R_R0 = 0, //16 64 bit data registers
    R_R1,
    R_R2,
    R_R3,
    R_R4,
    R_R5,
    R_R6,
    R_R7,
    R_R8, 
    R_R9,
    R_R10,
    R_R11,
    R_R12,
    R_R13,
    R_R14,
    R_R15,

    R_PC,    // program counter
    R_S,     // stack pointer
    R_COND,  // condition flags
    
    R_COUNT, 

    FL_POS = 1 << 0,
    FL_ZRO = 1 << 1,
    FL_NEG = 1 << 2,

    OP_NOP = 0,
    OP_ADD, 
    OP_SUB, 
    OP_MUL, 
    OP_SMUL, 
    OP_DIV, 
    OP_SDIV,
    OP_AND, 
    OP_OR, 
    OP_XOR, 
    OP_SHR, 
    OP_SHL, 
    OP_NOT, 
    OP_JMP, 
    OP_JZ, 
    OP_JNZ,
    OP_JP,
    OP_JN,
    OP_MOV,
    OP_ST,
    OP_LD,
    OP_COUNT,
    OP_UNKNOWN = -1,
};

inline u64 sign_extend(u64 x, s64 bit_count){
    if((x >> (bit_count-1)) & 1){
        x |= (0xFFFFFFFFFFFFFFFF << bit_count);
    }
    return x;
}

//this is probably inefficient
struct InstrRead{
    u64 OP;

    u64 DR;
    u64 QR;
    u64 RR;
    u64 SR1;
    u64 SR2;

    u64 immcond;
    u64 immval;
};

InstrRead ReadInstr(u64 instr){
    InstrRead read = {0};
    read.OP = instr >> 58;
    switch(read.OP){
        case OP_ADD:{
            read.DR = readbits(54, 4);
            read.SR1 = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_SUB:{
            read.DR = readbits(54, 4);
            read.SR1 = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_MUL:{
            read.DR = readbits(54, 4);
            read.SR1 = readbits(50, 4);
            if(readbits(49, 1))  read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                 read.SR2 = readbits(45, 4);
        }break;
        case OP_SMUL:{
            read.DR = readbits(54, 4);
            read.SR1 = readbits(50, 4);
            if(readbits(49, 1))  read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                 read.SR2 = readbits(45, 4);
        }break;
        case OP_DIV:{
            read.QR = readbits(54, 4);
            read.RR = readbits(50, 4);
            read.SR1 = readbits(46, 4);
            if(readbits(45, 1))  read.immval = sign_extend(readbits(0, 44), 44), read.immcond = 1;
            else                 read.SR2 = readbits(41, 4);
        }break;
        case OP_SDIV:{
            read.QR = readbits(54, 4);
            read.RR = readbits(50, 4);
            read.SR1 = readbits(46, 4);
            if(readbits(45, 1)) read.immval = sign_extend(readbits(0, 44), 44), read.immcond = 1;
            else                read.SR2 = readbits(41, 4);
        }break;
        case OP_AND:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_OR:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_XOR:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_SHR:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_SHL:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
            if(readbits(49, 1)) read.immval = sign_extend(readbits(0, 48), 48), read.immcond = 1;
            else                read.SR2 = readbits(45, 4);
        }break;
        case OP_NOT:{
            read.DR   = readbits(54, 4);
            read.SR1  = readbits(50, 4);
        }break;
        case OP_JZ:
        case OP_JNZ:
        case OP_JP:
        case OP_JN:
        case OP_JMP:{
            if(readbits(57,1)) read.immval = sign_extend(readbits(0, 56), 56), read.immcond = 1;
            else               read.SR1 = readbits(53, 4);
        }break;
        case OP_MOV:{
            read.DR = readbits(54, 4);
            if(readbits(53, 1)) read.immval = sign_extend(readbits(0, 52), 52), read.immcond = 1;
            else                read.SR1 = readbits(49,4);
        }break;
        case OP_LD:
        case OP_ST:{
            read.DR = readbits(54, 4);
            read.SR1 = readbits(50, 4);
        }break;
    }
    return read;
}

struct nasauMachine{
    Reg reg[R_COUNT];
    u8* mem;
    u64 mem_size;
};//machine

void nasau_init_machine(nasauMachine* machine, u8* memory, u64 memory_size){
    memset(machine, 0, sizeof(nasauMachine));
    machine->mem = memory;
    machine->mem_size = memory_size;
}

void mem_write_u8 (nasauMachine* machine,u64 address, u8  val){ machine->mem[address] = val; }
void mem_write_u16(nasauMachine* machine,u64 address, u16 val){ *(u16*)(machine->mem+address) = val; }
void mem_write_u32(nasauMachine* machine,u64 address, u32 val){ *(u32*)(machine->mem+address) = val; }
void mem_write_u64(nasauMachine* machine,u64 address, u64 val){ *(u64*)(machine->mem+address) = val; }
u8   mem_read_u8  (nasauMachine* machine,u64 address){ return *(u8*)(machine->mem + address); }
u16  mem_read_u16 (nasauMachine* machine,u64 address){ return *(u16*)(machine->mem + address); }
u32  mem_read_u32 (nasauMachine* machine,u64 address){ return *(u32*)(machine->mem + address); }
u64  mem_read_u64 (nasauMachine* machine,u64 address){ return *(u64*)(machine->mem + address); }
void update_flags (nasauMachine* machine,u64 r){
    if     (ureg(r)==0)  ureg(R_COND)=FL_ZRO;
    else if(ureg(r)>>63) ureg(R_COND)=FL_NEG;
    else                 ureg(R_COND)=FL_POS;
}

void nasau_tick(nasauMachine* machine){
    u64 instr = mem_read_u64(machine,reg[R_PC].u++ * sizeof(u64));  //get current instruction
    InstrRead read = ReadInstr(instr);

    switch(read.OP){
        case OP_ADD:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) + read.immval;
            else             ureg(read.DR) = ureg(read.SR1) + ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_SUB:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) - read.immval;
            else             ureg(read.DR) = ureg(read.SR1) - ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_MUL:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) * read.immval;
            else             ureg(read.DR) = ureg(read.SR1) * ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_SMUL:{
            if(read.immcond) sreg(read.DR) = sreg(read.SR1) * *(s64*)&read.immval;
            else             sreg(read.DR) = sreg(read.SR1) * sreg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_DIV:{
            if(read.immcond){
                ureg(read.QR) = ureg(read.SR1) / read.immval;
                ureg(read.RR) = ureg(read.SR1) % read.immval;
            }
            else{
                ureg(read.QR) = ureg(read.SR1) / ureg(read.SR2);
                ureg(read.RR) = ureg(read.SR1) % ureg(read.SR2);
            }
            update_flags(machine, read.DR);
        }break;
        case OP_SDIV:{
            if(read.immcond){
                sreg(read.QR) = sreg(read.SR1) / *(s64*)read.immval;
                sreg(read.RR) = sreg(read.SR1) % *(s64*)read.immval;
            }
            else{
                sreg(read.QR) = sreg(read.SR1) / sreg(read.SR2);
                sreg(read.RR) = sreg(read.SR1) % sreg(read.SR2);
            }
            update_flags(machine, read.DR);
        }break;
        case OP_AND:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) & read.immval;
            else             ureg(read.DR) = ureg(read.SR1) & ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_OR:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) | read.immval;
            else             ureg(read.DR) = ureg(read.SR1) | ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_XOR:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) ^ read.immval;
            else             ureg(read.DR) = ureg(read.SR1) ^ ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_SHR:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) >> read.immval;
            else             ureg(read.DR) = ureg(read.SR1) >> ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_SHL:{
            if(read.immcond) ureg(read.DR) = ureg(read.SR1) << read.immval;
            else             ureg(read.DR) = ureg(read.SR1) << ureg(read.SR2);
            update_flags(machine, read.DR);
        }break;
        case OP_NOT:{
            ureg(read.DR) = !ureg(read.SR1);
            update_flags(machine, read.DR);
        }break;
        case OP_JMP:{
            if(read.immcond) ureg(R_PC) = read.immval;
            else             ureg(R_PC) = ureg(read.SR1);
        }break;
        case OP_JZ:{
            if(ureg(R_COND) & FL_ZRO){
                if(read.immcond) ureg(R_PC) = read.immval;
                else             ureg(R_PC) = ureg(read.SR1);
            } 
        }break;
        case OP_JNZ:{
            if(!(ureg(R_COND) & FL_ZRO)){
                if(read.immcond) ureg(R_PC) = read.immval;
                else             ureg(R_PC) = ureg(read.SR1);
            } 
        }break;
        case OP_JP:{
            if(ureg(R_COND) & FL_POS){
                if(read.immcond) ureg(R_PC) = read.immval;
                else             ureg(R_PC) = ureg(read.SR1);
            } 
        }break;
        case OP_JN:{
            if(ureg(R_COND) & FL_NEG){
                if(read.immcond) ureg(R_PC) = read.immval;
                else             ureg(R_PC) = ureg(read.SR1);
            } 
        }break;
        case OP_MOV:{
            if(read.immcond) ureg(read.DR) = read.immval;
            else             ureg(read.DR) = ureg(read.SR1);
        }break;
        case OP_ST:{
            mem_write_u64(machine, ureg(read.DR), ureg(read.SR1));
        }break; 
        case OP_LD:{
            ureg(read.DR) = mem_read_u64(machine, ureg(read.SR1));
        }break;
    }//switch(read.OP)
}//tick()

}
#endif
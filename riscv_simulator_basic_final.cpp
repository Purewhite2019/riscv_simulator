#include <iostream>
#include <fstream>
#include <iomanip>
#include <cstring>
// #define LOCAL
// #define DEBUG_PAUSE
// #define DEBUG_READ
// #define DEBUG_IF
// #define DEBUG_ID
// #define DEBUG_EX
// #define DEBUG_MEM
// #define DEBUG_WB
// #define DEBUG_LN
using std::ifstream;
using std::cin;
using std::cout;
using std::endl;
using std::hex;
using std::dec;

bool isRunning = true;
int IF_FlushCount = 0;
int8_t* mem;
int32_t reg[32] = {0}, pc = 0;
int32_t &zero = reg[0], &ra = reg[1], &sp = reg[2], &gp = reg[3], &tp = reg[4], &t0 = reg[5], &t1 = reg[6], &t2 = reg[7], \
    &s0_fp = reg[8], &s1 = reg[9], &a0 = reg[10], &a1 = reg[11], &a2 = reg[12], &a3 = reg[13], &a4 = reg[14], &a5 = reg[15], \
    &a6 = reg[16], &a7 = reg[17], &s2 = reg[18], &s3 = reg[19], &s4 = reg[20], &s5 = reg[21], &s6 = reg[22], &s7 = reg[23], \
    &s8 = reg[24], &s9 = reg[25], &s10 = reg[26], &s11 = reg[27], &t3 = reg[28], &t4 = reg[29], &t5 = reg[30], &t6 = reg[31];
const char* regname[] = {"zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"};

struct IF_ID_Buffer{
    int32_t npc, ir;
} if_id_buffer;
struct ID_EX_Buffer{
    int32_t npc, ir, a, b, imm;
} id_ex_buffer;
struct EX_MEM_Buffer{
    int32_t npc, ir, aluoutput, b;
    bool cond;
} ex_mem_buffer;
struct MEM_WB_Buffer{
    int32_t ir, aluoutput;
} mem_wb_buffer;

class BranchPredictor_2bit{
    private:
        int HitCount = 0, TotCount = 0;
        int32_t Another_PC = 0, Last_PC = 0;
        int8_t buffer[0xff] = {0};
        bool Last_Prediction = false;
        // int32_t Another_PC[16] = {0};
        // bool Last_Prediction[16] = {false};
        // int iter = -1;
    public:
        void clear(){
            HitCount = 0;
            TotCount = 0;
            Another_PC = 0;
            Last_PC = 0;
            Last_Prediction = false;
            memset(buffer, 0, sizeof(buffer));
        }
        bool Predict(int32_t addr){
            Last_PC = addr;
            ++TotCount;
            if(buffer[addr&0xff] > 1){
                Last_Prediction = true;
                return true;
            }
            else{
                Last_Prediction = false;
                return false;
            }
        }
        bool LastPrediction(){return Last_Prediction;}
        void FeedBack(bool Fact){
            if(Fact && (buffer[Last_PC&0xff] < 3))
                ++buffer[Last_PC&0xff];
            if(!Fact && (buffer[Last_PC&0xff] > 0))
                --buffer[Last_PC&0xff];
            if(Fact == Last_Prediction)
                ++HitCount;
        }
        void PushPC(int32_t APC){Another_PC = APC;}
        int32_t PopPC(){return Another_PC;}
        void ShowAccuracy(){
            cout << "Prediction Accuracy: " << dec << HitCount << '/' << TotCount << ' ' << std::setprecision(2) << (double)HitCount/TotCount*100 << '%' << endl;
        }
} predictor;

int32_t sign_extend(int32_t x, int32_t n){
    int32_t high = x & (1<<(n-1));
    for(int32_t i = n+1; i <= 32; ++i)
        x |= (high <<= 1);
    return x;
}

int32_t stoi(char *s, int32_t digit){
    int32_t ret = 0;
    for(int32_t i = 0; i < digit; ++i){
        ret <<= 4;
        ret |= (s[i] <= '9' && s[i] >= '0') ? (s[i]-'0') : (s[i]-'A'+10);
    }
    return ret;
}

void clear(){
    isRunning = true;
    pc = 0;
    // pc = -4;
    memset(reg, 0, sizeof(reg));
    memset(mem, 0, 1048576*sizeof(int8_t));
    memset(&if_id_buffer, 0, sizeof(if_id_buffer));
    // if_id_buffer.npc = -1;
    memset(&id_ex_buffer, 0, sizeof(id_ex_buffer));
    // id_ex_buffer.npc = -1;
    memset(&ex_mem_buffer, 0, sizeof(ex_mem_buffer));
    // ex_mem_buffer.npc = -1;
    memset(&mem_wb_buffer, 0, sizeof(mem_wb_buffer));
}

void readsrc(const char *srcname, int8_t* &mem){
    #ifdef DEBUG_READ
        cout << "Reading Binary Source Code..." << endl;
    #endif // DEBUG_READ
    clear();
    ifstream src(srcname, ifstream::in);
    int32_t iter = 0;
    char l1[9], l2[9], l3[9], l4[9];
    while(true){
        src >> l4;
        if(src.fail()) break;
        if(l4[0] == '@'){
            iter = stoi(l4+1, 8);
            #ifdef DEBUG_READ
            cout << l4 << " @" << std::hex << iter << endl;
            #endif // DEBUG_READ
        }
        else{
            src >> l3 >> l2 >> l1;
            *(int32_t*)(mem+iter) = stoi(l4, 2) | (stoi(l3, 2) << 8) | (stoi(l2,2) << 16) | (stoi(l1, 2) << 24);
            iter += 4;
            #ifdef DEBUG_READ
            cout << l4 << l3 << l2 << l1 << ' ' << std::hex << ((int32_t*)mem)[(iter-4)/4] << endl;
            #endif // DEBUG_READ
        }
    }
    #ifdef DEBUG_READ
        cout << "Source Code Reading Finished." << endl;
    #endif // DEBUG_READ
    src.close();
}

void readsrc(int8_t* &mem){
    #ifdef DEBUG_READ
        cout << "Reading Binary Source Code..." << endl;
    #endif // DEBUG_READ
    clear();
    int32_t iter = 0;
    char l1[9], l2[9], l3[9], l4[9];
    while(true){
        cin >> l4;
        if(cin.eof()) break;
        if(l4[0] == '@'){
            #ifdef DEBUG_READ
            cout << l4 << " @";
            #endif
            iter = stoi(l4+1, 8);
            #ifdef DEBUG_READ
            cout << std::hex << iter << endl;
            #endif // DEBUG_READ
        }
        else{
            cin >> l3 >> l2 >> l1;
            #ifdef DEBUG_READ
            cout << l4 << l3 << l2 << l1 << ' ';
            #endif // DEBUG_READ
            *(int32_t*)(mem+iter) = stoi(l4, 2) | (stoi(l3, 2) << 8) | (stoi(l2,2) << 16) | (stoi(l1, 2) << 24);
            iter += 4;
            #ifdef DEBUG_READ
            cout << std::hex << ((int32_t*)mem)[(iter-4)/4] << endl;
            #endif // DEBUG_READ
        }
    }
    #ifdef DEBUG_READ
        cout << "Source Code Reading Finished." << endl;
    #endif // DEBUG_READ
}

void IF(){
    if(IF_FlushCount){
        
        --IF_FlushCount;
        if_id_buffer.ir = 0;
        #ifdef DEBUG_IF
        cout << "IF: Flushed. Flush Cycle Left: " << IF_FlushCount << endl;
        #endif
        return;
    }

    if_id_buffer.ir = *(int32_t*)(mem+pc);

    #ifdef DEBUG_IF
    cout << "IF: Read IR " << hex << if_id_buffer.ir  << " at " << pc;
    #endif

    if(((id_ex_buffer.ir & 0b1111111) == 0b0000011) // Load: MemRead == true
    && (((id_ex_buffer.ir>>7) & 0b11111) != 0)
    && ((((id_ex_buffer.ir>>7) & 0b11111) == ((if_id_buffer.ir>>15) & 0b11111))
     || (((id_ex_buffer.ir>>7) & 0b11111) == ((if_id_buffer.ir>>20) & 0b11111)))
    ){
        #ifdef DEBUG_IF
        cout << ", MemRead-RegRead Data Hazard Triggered!" << endl;
        #endif
        if_id_buffer.ir = 0;
        return;
    }

    if_id_buffer.npc = (pc += 4);

    #ifdef DEBUG_IF
    cout << ", New PC " << if_id_buffer.npc << endl;
    #endif
}

void ID(){
    id_ex_buffer.ir = if_id_buffer.ir;
    id_ex_buffer.npc = if_id_buffer.npc;
    #ifdef DEBUG_ID
    cout << "ID: IR: " << hex << if_id_buffer.ir << ' ';
    #endif

    switch(id_ex_buffer.ir & 0b1111111){ // Decoding
        case 0b0000011: // LB LH LW LBU LHU
             // rd = (ir>>7) & 0b11111;  // Storage target
            // rs1 = (ir>>15) & 0b11111;
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.imm = sign_extend((id_ex_buffer.ir>>20) & 0b111111111111, 12);
            IF_FlushCount = 3;
            #ifdef DEBUG_ID
            cout << "Read L";
            #endif
            break;
        case 0b0010011: // ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI
            // rd = (ir>>7) & 0b11111;  // Storage target
            // rs1 = (ir>>15) & 0b11111;
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.imm = sign_extend((id_ex_buffer.ir>>20) & 0b111111111111, 12);
            #ifdef DEBUG_ID
            cout << "Read ALUI";
            #endif
            break;

        case 0b0100011: // SB SH SW
            // rs1 = (ir>>15) & 0b11111;
            // rs2 = (ir>>20) & 0b11111;    // Storage target
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.b = reg[(id_ex_buffer.ir>>20) & 0b11111];
            id_ex_buffer.imm = sign_extend((((id_ex_buffer.ir>>25) & 0b1111111)<<5) | ((id_ex_buffer.ir>>7) & 0b11111), 12);
            IF_FlushCount = 3;
            #ifdef DEBUG_ID
            cout << "Read S... ";
            #endif
            break;
        // pc的计算和调整在Data Hazard处理后
        case 0b1100111: // JALR
            // rd = (ir>>7) & 0b11111;  // Storage target
            // rs1 = (ir>>15) & 0b11111;
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.imm = sign_extend((id_ex_buffer.ir>>20) & 0b111111111111, 12);
            #ifdef DEBUG_ID
            cout << "Read JALR... ";
            #endif
            break;

        case 0b1101111: // JAL
            id_ex_buffer.imm = sign_extend((((id_ex_buffer.ir>>31)&1)<<20) | (((id_ex_buffer.ir>>21) & 0b1111111111)<<1) | (((id_ex_buffer.ir>>20)&1)<<11) | (id_ex_buffer.ir & (0b11111111<<12)), 21);
            #ifdef DEBUG_ID
            cout << "Read JAL... ";
            #endif
            break;

        case 0b1100011: // BEQ BNE BLT BGE BLTU BGEU
            // rs1 = (ir>>15) & 0b11111;
            // rs2 = (ir>>20) & 0b11111;
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.b = reg[(id_ex_buffer.ir>>20) & 0b11111];
            id_ex_buffer.imm = sign_extend((((id_ex_buffer.ir>>7)&1)<<11) | (((id_ex_buffer.ir>>8)&0b1111)<<1) | (((id_ex_buffer.ir>>25)&0b111111)<<5) | (((id_ex_buffer.ir>>31)&1)<<12), 13);

            #ifdef DEBUG_ID
            cout << "Read B... ";
            #endif
            break;

        case 0b0110011: // ADD SUB SLL SLT SLTU XOR SRL SRA OR AND
            // rs1 = (ir>>15) & 0b11111;
            // rs2 = (ir>>20) & 0b11111;
            id_ex_buffer.a = reg[(id_ex_buffer.ir>>15) & 0b11111];
            id_ex_buffer.b = reg[(id_ex_buffer.ir>>20) & 0b11111];
            #ifdef DEBUG_ID
            cout << "Read ALU... ";
            #endif
            break;

        case 0b0110111: // LUI
        case 0b0010111: // AUIPC
            id_ex_buffer.imm = id_ex_buffer.ir & (0b11111111111111111111<<12);
            #ifdef DEBUG_ID
            cout << "Read LUI | AUIPC... ";
            #endif
            break;
    }

    // 先MEM Hazard，后EX Hazard，保证如果EX和MEM都可以Forward到同一个reg，EX结果是最终结果
    // TODO: What happened to the Hazard Process?

    if(  (((mem_wb_buffer.ir & 0b1111111) == 0b0110111)   // LUI
        ||((mem_wb_buffer.ir & 0b1111111) == 0b0010111)   // AUIPC
        ||((mem_wb_buffer.ir & 0b1111111) == 0b1101111)   // JAL
        ||((mem_wb_buffer.ir & 0b1111111) == 0b1100111)   // JALR
        ||((mem_wb_buffer.ir & 0b1111111) == 0b0010011)   // ALUI
        ||((mem_wb_buffer.ir & 0b1111111) == 0b0110011)   // ALU
        ||((mem_wb_buffer.ir & 0b1111111) == 0b0000011))  // LOAD
    && (((mem_wb_buffer.ir>>7) & 0b11111) != 0)){
        if(((mem_wb_buffer.ir>>7) & 0b11111) == ((id_ex_buffer.ir>>15) & 0b11111)){
            #ifdef DEBUG_ID
            cout << "MEM Data Hazard Triggered!" << endl;
            #endif
            id_ex_buffer.a = mem_wb_buffer.aluoutput;
        }
        if(((mem_wb_buffer.ir>>7) & 0b11111) == ((id_ex_buffer.ir>>20) & 0b11111)){
            #ifdef DEBUG_ID
            cout << "MEM Data Hazard Triggered!" << endl;
            #endif
            id_ex_buffer.b = mem_wb_buffer.aluoutput;
        }
    }

    if(  (((ex_mem_buffer.ir & 0b1111111) == 0b0110111)     // LUI
        ||((ex_mem_buffer.ir & 0b1111111) == 0b0010111)     // AUIPC
        ||((ex_mem_buffer.ir & 0b1111111) == 0b1101111)     // JAL
        ||((ex_mem_buffer.ir & 0b1111111) == 0b1100111)     // JALR
        ||((ex_mem_buffer.ir & 0b1111111) == 0b0010011)     // ALUI
        ||((ex_mem_buffer.ir & 0b1111111) == 0b0110011))    // ALU
    &&(((ex_mem_buffer.ir>>7) & 0b11111) != 0)){
        if(((ex_mem_buffer.ir>>7) & 0b11111) == ((id_ex_buffer.ir>>15) & 0b11111)){
            #ifdef DEBUG_ID
            cout << "EX Data Hazard Triggered!" << endl;
            #endif
            id_ex_buffer.a = ex_mem_buffer.aluoutput;
        }
        if(((ex_mem_buffer.ir>>7) & 0b11111) == ((id_ex_buffer.ir>>20) & 0b11111)){
            #ifdef DEBUG_ID
            cout << "EX Data Hazard Triggered!" << endl;
            #endif
            id_ex_buffer.b = ex_mem_buffer.aluoutput;
        }
    }

    switch(id_ex_buffer.ir & 0b1111111){
        case 0b1100111: // JALR
            pc = (id_ex_buffer.a + id_ex_buffer.imm)&(~1);
            break;
        case 0b1101111: // JAL
            pc = id_ex_buffer.npc - 4 + id_ex_buffer.imm;
            break;
        case 0b1100011: // B
            if(predictor.Predict(pc-4)){
                predictor.PushPC(pc);
                pc = id_ex_buffer.npc - 4 + id_ex_buffer.imm;
            }
            else predictor.PushPC(id_ex_buffer.npc - 4 + id_ex_buffer.imm);
            break;
    }

    #ifdef DEBUG_ID
    cout << "a: " << hex << id_ex_buffer.a << " b: " << hex << id_ex_buffer.b << " imm hex: " << id_ex_buffer.imm << " imm dec: " << dec << id_ex_buffer.imm << endl;
    #endif
}

void EX(){
    ex_mem_buffer.ir =  id_ex_buffer.ir;
    ex_mem_buffer.npc =  id_ex_buffer.npc;
    ex_mem_buffer.cond = false;
    #ifdef DEBUG_EX
    cout << "EX: IR: " << hex << id_ex_buffer.ir << endl;
    #endif
    switch(ex_mem_buffer.ir & 0b1111111){
        case 0b0000011: // LB LH LW LBU LHU
            ex_mem_buffer.aluoutput = id_ex_buffer.a + id_ex_buffer.imm;
            break;

        case 0b0010011: // ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI
            switch((ex_mem_buffer.ir>>12)&0b111){
                case 0b000: // ADDI
                    ex_mem_buffer.aluoutput = id_ex_buffer.a + id_ex_buffer.imm;
                    break;

                case 0b010: // SLTI
                    ex_mem_buffer.aluoutput = (id_ex_buffer.a < id_ex_buffer.imm);
                    break;

                case 0b011: // SLTIU
                    ex_mem_buffer.aluoutput = ((uint32_t)id_ex_buffer.a < (uint32_t)id_ex_buffer.imm);
                    break;

                case 0b100: // XORI
                    ex_mem_buffer.aluoutput = id_ex_buffer.a ^ id_ex_buffer.imm;
                    break;

                case 0b110: // ORI
                    ex_mem_buffer.aluoutput = id_ex_buffer.a | id_ex_buffer.imm;
                    break;

                case 0b111: // ANDI
                    ex_mem_buffer.aluoutput = id_ex_buffer.a & id_ex_buffer.imm;
                    break;

                case 0b001:   // SLLI
                    ex_mem_buffer.aluoutput = id_ex_buffer.a << id_ex_buffer.imm;
                    break;

                case 0b101:   // SRLI | SRAI
                    if((id_ex_buffer.imm>>10)&1){  // SRAI
                        ex_mem_buffer.aluoutput = id_ex_buffer.a >> (id_ex_buffer.imm&0b111111);
                        #ifdef DEBUG_EX
                        cout << " SRAI ";
                        #endif
                    }
                    else{    // SRLI
                        ex_mem_buffer.aluoutput = (uint32_t)id_ex_buffer.a >> (uint32_t)(id_ex_buffer.imm&0b111111);
                        #ifdef DEBUG_EX
                        cout << " SRLI ";
                        #endif
                    }
                    break;
            }
            break;

        case 0b1100111: // JALR
            ex_mem_buffer.aluoutput = ex_mem_buffer.npc;    // to x[rd]
            break;

        case 0b0100011: // SB SH SW
            ex_mem_buffer.aluoutput = id_ex_buffer.a + id_ex_buffer.imm;
            switch((ex_mem_buffer.ir>>12)&0b111){
                case 0b000: // SB
                    ex_mem_buffer.b = id_ex_buffer.b & 0b11111111;
                    break;

                case 0b001: // SH
                    ex_mem_buffer.b = id_ex_buffer.b & 0b1111111111111111;
                    break;

                case 0b010: // SW
                    ex_mem_buffer.b = id_ex_buffer.b;
                    break;
            }
            break;

        case 0b1100011: // BEQ BNE BLT BGE BLTU BGEU
            switch((ex_mem_buffer.ir>>12)&0b111){
                case 0b000: // BEQ
                    if(id_ex_buffer.a == id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;

                case 0b001: // BNE
                    if(id_ex_buffer.a != id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;

                case 0b100: // BLT
                    if(id_ex_buffer.a < id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;

                case 0b101: // BGE
                    if(id_ex_buffer.a >= id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;

                case 0b110: // BLTU
                    if((uint32_t)id_ex_buffer.a < (uint32_t)id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;

                case 0b111: // BGEU
                    if((uint32_t)id_ex_buffer.a >= (uint32_t)id_ex_buffer.b){
                        ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
                        ex_mem_buffer.cond = true;
                    }
                    else ex_mem_buffer.cond = false;
                    break;
            }
            if(ex_mem_buffer.cond) predictor.FeedBack(true);
            else predictor.FeedBack(false);

            if(ex_mem_buffer.cond != predictor.LastPrediction()){
                if_id_buffer.ir = 0;
                id_ex_buffer.ir = 0;
                pc = predictor.PopPC();
            }
            break;

        case 0b0110011: // ADD SUB SLL SLT SLTU XOR SRL SRA OR AND
            switch((ex_mem_buffer.ir>>12)&0b111){
                case 0b000: // ADD | SUB
                    if((ex_mem_buffer.ir>>30)&1)   // SUB
                        ex_mem_buffer.aluoutput = id_ex_buffer.a - id_ex_buffer.b;
                    else   // ADD
                        ex_mem_buffer.aluoutput = id_ex_buffer.a + id_ex_buffer.b;
                    break;

                case 0b001: // SLL
                    ex_mem_buffer.aluoutput = id_ex_buffer.a << id_ex_buffer.b;
                    break;

                case 0b010: // SLT
                    ex_mem_buffer.aluoutput = (id_ex_buffer.a < id_ex_buffer.b);
                    break;

                case 0b011: // SLTU
                    ex_mem_buffer.aluoutput = ((uint32_t)id_ex_buffer.a < (uint32_t)id_ex_buffer.b);
                    break;

                case 0b100: // XOR
                    ex_mem_buffer.aluoutput = id_ex_buffer.a ^ id_ex_buffer.b;
                    break;

                case 0b101: // SRL | SRA
                    if((ex_mem_buffer.ir>>30)&1)   // SRA
                        ex_mem_buffer.aluoutput = id_ex_buffer.a >> id_ex_buffer.b;
                    else   // SRL
                        ex_mem_buffer.aluoutput = (uint32_t)id_ex_buffer.a >> (uint32_t)id_ex_buffer.b;
                    break;
                    
                case 0b110: // OR
                    ex_mem_buffer.aluoutput = id_ex_buffer.a | id_ex_buffer.b;
                    break;

                case 0b111: // AND
                    ex_mem_buffer.aluoutput = id_ex_buffer.a & id_ex_buffer.b;
                    break;
            }
            break;
        case 0b0110111: // LUI
            ex_mem_buffer.aluoutput = id_ex_buffer.imm;
            break;

        case 0b1101111: // JAL
            ex_mem_buffer.aluoutput = ex_mem_buffer.npc;    // to x[rd]
            break;

        case 0b0010111: // AUIPC
            ex_mem_buffer.aluoutput = ex_mem_buffer.npc - 4 + id_ex_buffer.imm;
            break;
    }
}

void MEM(){
    mem_wb_buffer.ir = ex_mem_buffer.ir;

    #ifdef DEBUG_MEM
    cout << "MEM: IR: " << hex << ex_mem_buffer.ir << ' ';
    #endif
    switch(mem_wb_buffer.ir & 0b1111111){
        case 0b0000011: // LB LH LW LBU LHU
            switch((mem_wb_buffer.ir>>12)&0b111){
                case 0b000: // LB
                    mem_wb_buffer.aluoutput = sign_extend((*(int32_t*)(mem+ex_mem_buffer.aluoutput)) & 0b11111111, 8);
                    break;
                case 0b001: // LH
                    mem_wb_buffer.aluoutput = sign_extend(*(int32_t*)(mem+ex_mem_buffer.aluoutput) & 0b1111111111111111, 16);
                    break;
                case 0b010: // LW
                    mem_wb_buffer.aluoutput = *(int32_t*)(mem+ex_mem_buffer.aluoutput);
                    break;
                case 0b100: // LBU
                    mem_wb_buffer.aluoutput = (*(int32_t*)(mem+ex_mem_buffer.aluoutput)) & 0b11111111;
                    break;
                case 0b101:  // LHU
                    mem_wb_buffer.aluoutput = (*(int32_t*)(mem+ex_mem_buffer.aluoutput)) & 0b1111111111111111;
                    break;
            }
            #ifdef DEBUG_MEM
            cout << "Read " << hex << mem_wb_buffer.aluoutput << " dec: " << dec << mem_wb_buffer.aluoutput << " at " << hex << ex_mem_buffer.aluoutput;
            #endif
            break;

        case 0b0100011: // SB SH SW
            switch((mem_wb_buffer.ir>>12)&0b111){
                case 0b000: // SB
                    *(int32_t*)(mem+ex_mem_buffer.aluoutput) &= (0b111111111111111111111111<<8);
                    *(int32_t*)(mem+ex_mem_buffer.aluoutput) |= ex_mem_buffer.b;
                    break;
                case 0b001: // SH
                    *(int32_t*)(mem+ex_mem_buffer.aluoutput) &= (0b1111111111111111<<16);
                    *(int32_t*)(mem+ex_mem_buffer.aluoutput) |= ex_mem_buffer.b;
                    break;
                case 0b010: // SW
                    *(int32_t*)(mem+ex_mem_buffer.aluoutput) = ex_mem_buffer.b;
                    break;
            }
            #ifdef DEBUG_MEM
            cout << "Save " << hex << ex_mem_buffer.b << " dec: " << dec << ex_mem_buffer.b << " at " << hex << ex_mem_buffer.aluoutput;
            #endif
            break;
        
        default:
            mem_wb_buffer.aluoutput = ex_mem_buffer.aluoutput;
            break;
    }
    #ifdef DEBUG_MEM
    cout << endl;
    #endif
}

void WB(){
    #ifdef DEBUG_WB
    cout << "WB: IR: " << hex << mem_wb_buffer.ir << ' ';
    #endif
    if(mem_wb_buffer.ir == 0x0ff00513){  // 放在WB()，保证所有指令都执行完成(而且多余的MEM()不会修改返回值)
        isRunning = false;
        #ifdef DEBUG_WB
        cout << "Read 0x0ff00513, halt..." << endl;
        #endif
        return;
    }
    switch(mem_wb_buffer.ir & 0b1111111){
        case 0b0000011: // LB LH LW LBU LHU
        case 0b0010011: // ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI
        case 0b0110011: // ADD SUB SLL SLT SLTU XOR SRL SRA OR AND
        case 0b0110111: // LUI
        case 0b0010111: // AUIPC
        case 0b1101111: // JAL
        case 0b1100111: // JALR
            if(((mem_wb_buffer.ir>>7) & 0b11111) != 0){
                reg[(mem_wb_buffer.ir>>7) & 0b11111] = mem_wb_buffer.aluoutput;
                #ifdef DEBUG_WB
                cout << "Write " << hex << mem_wb_buffer.aluoutput << " dec: " << dec << mem_wb_buffer.aluoutput << " into Reg." << regname[(mem_wb_buffer.ir>>7) & 0b11111];
                #endif
            }
            #ifdef DEBUG_WB
            else cout << "WRITE_INTO_ZERO triggered! value: " << hex << mem_wb_buffer.aluoutput << " dec: " << dec << mem_wb_buffer.aluoutput;
            #endif
            break;
    }
    #ifdef DEBUG_WB
    cout << endl;
    #endif
}

int test(const char *filename){
    readsrc(filename, mem);
    // while(true){    // 串行
    //     IF();
    //     ID();
    //     if(!isRunning) break;
    //     EX();
    //     MEM();
    //     WB();
    //     #ifdef DEBUG_LN
    //     cin.get();
    //     #endif
    // }
    while(isRunning){   // 并行
        WB();
        MEM();
        EX();
        ID();
        IF();
        #ifdef DEBUG_PAUSE
        cin.get();
        cout << endl;
        #endif
    }
    return (unsigned)(a0&0b11111111);
}

std::pair<const char*, int> obj[15] = {
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\sample\\sample.data", 94), 
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\naive.data", 94),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\lvalue2.data", 175),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\manyarguments.data", 40),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\gcd.data", 178),

    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\magic.data", 106),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\array_test1.data", 123),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\array_test2.data", 43),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\basicopt1.data", 88),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\bulgarian.data", 159),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\expr.data", 58),

    std::make_pair("E:\\Studio\\PPCA\\RISCV\\heart\\heart.data", 127),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\multiarray.data", 115),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\hanoi.data", 20),
    std::make_pair("E:\\Studio\\PPCA\\RISCV\\riscv-testcases\\testcases\\pi.data", 137),
};

void testall(){
    int ret = -1;
    bool isOK = true;
    for(int i = 0; i < 15; ++i){
        cout << "Testing \"" << obj[i].first << "\", Expect " << obj[i].second << "...";
        if((ret = test(obj[i].first)) == obj[i].second) cout << "OK" << endl;
        else {
            cout << "Failed, returned " << ret << endl;
            isOK = false;
        }
        cout << '\t';
        predictor.ShowAccuracy();
        predictor.clear();
    }
    if(isOK) cout << "All Tests are Accepted" << endl;
    else cout << "Failed" << endl;
    // predictor.ShowAccuracy();
}

int main(){
    // std::ios::sync_with_stdio(false); cin.tie(0); cout.tie(0);
    mem = new int8_t[1048576];
    #ifdef LOCAL
    char dir[256] = {0};
    cout << "Please input the directory of the source file. " << endl;
    cin >> dir;
    if(dir[0] == '*'){
        testall();
        return 0;
    }
    readsrc(dir, mem);
    #endif
    #ifndef LOCAL
    readsrc(mem);
    #endif
    while(isRunning){   // 并行
        WB();
        MEM();
        EX();
        ID();
        IF();
        #ifdef DEBUG_PAUSE
        cin.get();
        #endif
        #ifdef DEBUG_LN
        cout << endl;
        #endif
    }
    #ifdef LOCAL
    cout << "Return Value: " << hex << (unsigned)(a0&0b11111111) << " dec: " << dec << (unsigned)(a0&0b11111111) << endl;
    predictor.ShowAccuracy();
    #endif
    #ifndef LOCAL
    cout << dec << (unsigned)(a0&0b11111111) << endl;
    #endif
    return 0;
}
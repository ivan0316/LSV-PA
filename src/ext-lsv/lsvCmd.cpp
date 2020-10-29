#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <iostream>
#include <fstream> 
#include <map>
using namespace std; 

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_sopunate", Lsv_CommandPrintNodes, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk, int argc, char** argv) {
    Abc_Obj_t* pObj;
    int i;
    if(argc > 1){
        ofstream fout(argv[1]);
        fout << "a" << endl;
        fout.close(); 
    }
    ofstream fout("res.out");
    /*
    for(int i=0; i<argc; i++){
        std::cout << "  argv[" << i << "]: " << argv[i] << std::endl;
    }*/

    Abc_NtkForEachNode(pNtk, pObj, i) {
        // printf(".names ");
        Abc_Obj_t* pFanin;
        int j;
        /*
        Abc_ObjForEachFanin(pObj, pFanin, j) {
            printf("%s ", Abc_ObjName(pFanin));
        }
        */
        // printf("%s\n", Abc_ObjName(pObj));
        if (Abc_NtkHasSop(pNtk)) {
            size_t cntFanIn = 0;
            Abc_ObjForEachFanin(pObj, pFanin, j){
                cntFanIn++;
            }
            if(cntFanIn == 0)
                continue;
            // printf("%s", (char*)pObj->pData);
            char delim[] = "\n";
            char* copyData = (char*) calloc(strlen((char*)pObj->pData)+1, sizeof(char));
            strcpy(copyData, (char*)pObj->pData);
            char *ptr = strtok(copyData, delim);
            // a. allocate 2d space
            unsigned int numCol = 0, numRow = 0;
            bool isSOP = true;
            if(ptr != NULL){
                numCol = (unsigned)strlen(ptr)-2;
                // printf("# of col: %u\n", (unsigned)strlen(ptr)-2);
                isSOP = (ptr[numCol+1] == '1') ? true : false;
                // printf("is%sSOP\n", (isSOP ? " " : " not "));
            }
            while(ptr != NULL){
                numRow++;
                ptr = strtok(NULL, delim);
            }
            // printf("# of row: %u\n", numRow);
            char *arr = (char *)malloc(numRow * numCol * sizeof(char)); 
            // b. store data to 2d array
            strcpy(copyData, (char*)pObj->pData);
            ptr = strtok(copyData, delim);
            for(unsigned int iterI = 0; iterI < numRow; iterI++){
                for(unsigned int iterJ = 0; iterJ < numCol; iterJ++){
                    *(arr + iterI*numCol + iterJ) = ptr[iterJ];
                }
                ptr = strtok(NULL, delim);
            }
            // d. Determine is unate or not
            // row 0: has 0
            // row 1: has 1
            // row 2: has -
            bool *arrHas01 = (bool *)malloc(3 * numCol * sizeof(bool)); 
            for(size_t iterI = 0; iterI < 3; iterI++){
                for(size_t iterJ = 0; iterJ < numCol; iterJ++){
                    *(arrHas01 + iterI*numCol + iterJ) = false;
                }
            }
            for(size_t iterI = 0; iterI < numRow; iterI++){
                for(size_t iterJ = 0; iterJ < numCol; iterJ++){
                    if(*(arr + iterI*numCol + iterJ) == '0')
                        *(arrHas01 + 0*numCol + iterJ) = true;
                    else if(*(arr + iterI*numCol + iterJ) == '1')
                        *(arrHas01 + 1*numCol + iterJ) = true;
                    else
                        *(arrHas01 + 2*numCol + iterJ) = true;
                }
            }
            int *arrIsUnate = (int *)malloc(numCol * sizeof(int)); 
            int *arrHas012 = (int *)malloc(4 * sizeof(int)); 
            for(size_t iterI = 0; iterI < 4; iterI++)
                *(arrHas012 + iterI) = 0;
            // 0: negative unate
            // 1: positive unate
            // 2: binate
            // 3: both
            for(size_t iterJ = 0; iterJ < numCol; iterJ++){
                // deal with SOP
                // 2*2*2
                if(isSOP){
                    if((*(arrHas01 + 0*numCol + iterJ) == false) && (*(arrHas01 + 1*numCol + iterJ) == false)){
                        *(arrIsUnate + iterJ) = 3;
                        (*(arrHas012 + 3))++;
                    }
                    else if((*(arrHas01 + 0*numCol + iterJ) == false) && (*(arrHas01 + 1*numCol + iterJ) == true)){
                        *(arrIsUnate + iterJ) = 1;
                        (*(arrHas012 + 1))++;
                    }
                    else if((*(arrHas01 + 0*numCol + iterJ) == true) && (*(arrHas01 + 1*numCol + iterJ) == false)){
                        *(arrIsUnate + iterJ) = 0;
                        (*(arrHas012 + 0))++;
                    }
                    else{
                        *(arrIsUnate + iterJ) = 2;
                        (*(arrHas012 + 2))++;
                    }
                }
                else{
                    // ???
                    if((*(arrHas01 + 0*numCol + iterJ) == false) && (*(arrHas01 + 1*numCol + iterJ) == false)){
                        *(arrIsUnate + iterJ) = 3;
                        (*(arrHas012 + 3))++;
                    }
                    else if((*(arrHas01 + 0*numCol + iterJ) == false) && (*(arrHas01 + 1*numCol + iterJ) == true)){
                        *(arrIsUnate + iterJ) = 0;
                        (*(arrHas012 + 0))++;
                    }
                    else if((*(arrHas01 + 0*numCol + iterJ) == true) && (*(arrHas01 + 1*numCol + iterJ) == false)){
                        *(arrIsUnate + iterJ) = 1;
                        (*(arrHas012 + 1))++;
                    }
                    else{
                        *(arrIsUnate + iterJ) = 2;
                        (*(arrHas012 + 2))++;
                    }
                }
            }
            // e. Print unate or binate
            printf("node %s:\n", Abc_ObjName(pObj));
            fout << "node " << Abc_ObjName(pObj) << ":" << endl;
            size_t cnt = 0;
            if((*(arrHas012 + 1)+*(arrHas012 + 3)) != 0){
                printf("+unate inputs: ");
                fout << "+unate inputs: ";
                map<size_t, string> idToName;
                Abc_ObjForEachFanin(pObj, pFanin, j) {
                    // printf("id: %d\n", Abc_ObjId(pFanin));
                    if((*(arrIsUnate + j) == 1)||(*(arrIsUnate + j) == 3))
                        idToName[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
                }
                cnt = 0;
                for(auto it = idToName.begin(); it != idToName.end(); ++it){
                    cout << it->second;
                    cnt++;
                    if(cnt != (*(arrHas012 + 1)+*(arrHas012 + 3))){
                        cout << ",";
                        // fout << ",";
                    }
                }
                printf("\n");
                fout << endl;
            }
            cnt = 0;
            if((*(arrHas012 + 0)+*(arrHas012 + 3)) != 0){
                printf("-unate inputs: ");
                fout << "-unate inputs: ";
                map<size_t, string> idToName;
                Abc_ObjForEachFanin(pObj, pFanin, j) {
                    if((*(arrIsUnate + j) == 0)||(*(arrIsUnate + j) == 3))
                        idToName[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
                }
                cnt = 0;
                for(auto it = idToName.begin(); it != idToName.end(); ++it){
                    cout << it->second;
                    cnt++;
                    if(cnt != (*(arrHas012 + 0)+*(arrHas012 + 3))){
                        cout << ",";
                        // fout << ",";
                    }
                }
                printf("\n");
                fout << endl;
            }
            cnt = 0;
            if(*(arrHas012 + 2) != 0){
                printf("binate inputs: ");
                fout << "binate inputs: ";
                map<size_t, string> idToName;
                Abc_ObjForEachFanin(pObj, pFanin, j) {
                    if(*(arrIsUnate + j) == 2)
                        idToName[Abc_ObjId(pFanin)] = Abc_ObjName(pFanin);
                }
                cnt = 0;
                for(auto it = idToName.begin(); it != idToName.end(); ++it){
                    cout << it->second;
                    cnt++;
                    if(cnt != *(arrHas012 + 2)){
                        cout << ",";
                        // fout << ",";
                    }
                }
                printf("\n");
                fout << endl;
            }
        }
        //printf("\n");
        // fout << endl;
    }
    
    fout.close(); 
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk, argc, argv);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
# 1 "./hello.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./hello.cil.c"
# 5 "hello.c"
void __globinit_hello(void) ;
extern void __CrestInit(void) __attribute__((__crest_skip__)) ;
extern void __CrestGetMPIInfo(void) __attribute__((__crest_skip__)) ;
extern void __CrestWorldSizeWithLimit(unsigned long addr , int limit ) __attribute__((__crest_skip__)) ;
extern void __CrestRankNonDefaultComm2(long long val , unsigned long addr ) __attribute__((__crest_skip__)) ;
extern void __CrestRankNonDefaultComm1(unsigned long addr ) __attribute__((__crest_skip__)) ;
extern void __CrestRank(unsigned long addr ) __attribute__((__crest_skip__)) ;
extern void __CrestHandleReturn(int id , long long val ) __attribute__((__crest_skip__)) ;
extern void __CrestReturn(int id ) __attribute__((__crest_skip__)) ;
extern void __CrestCall(int id , unsigned int fid ) __attribute__((__crest_skip__)) ;
extern void __CrestBranch(int id , int bid , unsigned char b ) __attribute__((__crest_skip__)) ;
extern void __CrestApply2(int id , int op , long long val ) __attribute__((__crest_skip__)) ;
extern void __CrestApply1(int id , int op , long long val ) __attribute__((__crest_skip__)) ;
extern void __CrestClearStack(int id ) __attribute__((__crest_skip__)) ;
extern void __CrestStore(int id , unsigned long addr ) __attribute__((__crest_skip__)) ;
extern void __CrestLoad(int id , unsigned long addr , long long val ) __attribute__((__crest_skip__)) ;
# 265 "/usr/include/mpich/mpi.h"
typedef int MPI_Comm;
# 212 "/usr/lib/gcc/x86_64-linux-gnu/4.8/include/stddef.h"
typedef unsigned long size_t;
# 131 "/usr/include/x86_64-linux-gnu/bits/types.h"
typedef long __off_t;
# 132 "/usr/include/x86_64-linux-gnu/bits/types.h"
typedef long __off64_t;
# 44 "/usr/include/stdio.h"
struct _IO_FILE;
# 44 "/usr/include/stdio.h"
struct _IO_FILE;
# 48 "/usr/include/stdio.h"
typedef struct _IO_FILE FILE;
# 144 "/usr/include/libio.h"
struct _IO_FILE;
# 154 "/usr/include/libio.h"
typedef void _IO_lock_t;
# 160 "/usr/include/libio.h"
struct _IO_marker {
   struct _IO_marker *_next ;
   struct _IO_FILE *_sbuf ;
   int _pos ;
};
# 245 "/usr/include/libio.h"
struct _IO_FILE {
   int _flags ;
   char *_IO_read_ptr ;
   char *_IO_read_end ;
   char *_IO_read_base ;
   char *_IO_write_base ;
   char *_IO_write_ptr ;
   char *_IO_write_end ;
   char *_IO_buf_base ;
   char *_IO_buf_end ;
   char *_IO_save_base ;
   char *_IO_backup_base ;
   char *_IO_save_end ;
   struct _IO_marker *_markers ;
   struct _IO_FILE *_chain ;
   int _fileno ;
   int _flags2 ;
   __off_t _old_offset ;
   unsigned short _cur_column ;
   signed char _vtable_offset ;
   char _shortbuf[1] ;
   _IO_lock_t *_lock ;
   __off64_t _offset ;
   void *__pad1 ;
   void *__pad2 ;
   void *__pad3 ;
   void *__pad4 ;
   size_t __pad5 ;
   int _mode ;
   char _unused2[(15UL * sizeof(int ) - 4UL * sizeof(void *)) - sizeof(size_t )] ;
};
# 992 "/usr/include/mpich/mpi.h"
extern int MPI_Comm_size(MPI_Comm comm , int *size ) ;
# 993 "/usr/include/mpich/mpi.h"
extern int MPI_Comm_rank(MPI_Comm comm , int *rank ) ;
# 1030 "/usr/include/mpich/mpi.h"
extern int MPI_Get_processor_name(char *name , int *resultlen ) ;
# 1041 "/usr/include/mpich/mpi.h"
extern int MPI_Init(int *argc , char ***argv ) ;
# 1042 "/usr/include/mpich/mpi.h"
extern int MPI_Finalize(void) ;
# 169 "/usr/include/stdio.h"
extern struct _IO_FILE *stdout ;
# 242 "/usr/include/stdio.h"
extern int fflush(FILE *__stream ) ;
# 362 "/usr/include/stdio.h"
extern int printf(char const * __restrict __format , ...) ;
# 226 "/home/westwind/myInstall/Develop/compi/bin/../include/crest.h"
extern void __CrestIntWithLimit(int *x , long long limit ) __attribute__((__crest_skip__)) ;
# 5 "hello.c"
int main(int argc , char **argv )
{
  int world_rank ;
  int a ;
  int world_size ;
  int b ;
  char processor_name[128] ;
  int name_len ;
  int __retres9 ;

  {
  __globinit_hello();
  __CrestCall(2, 1);
  __CrestStore(1, (unsigned long )(& argc));
# 12 "hello.c"
  MPI_Init((int *)((void *)0), (char ***)((void *)0));
  __CrestGetMPIInfo();
# 14 "hello.c"
  __CrestIntWithLimit(& a, 100LL);
  __CrestLoad(5, (unsigned long )(& a), (long long )a);
  __CrestLoad(4, (unsigned long )0, (long long )1);
  __CrestApply2(3, 0, (long long )(a + 1));
  __CrestStore(6, (unsigned long )(& b));
# 16 "hello.c"
  b = a + 1;
  __CrestLoad(9, (unsigned long )(& a), (long long )a);
  __CrestLoad(8, (unsigned long )0, (long long )1);
  __CrestApply2(7, 0, (long long )(a + 1));
  __CrestStore(10, (unsigned long )(& a));
# 17 "hello.c"
  a ++;
  __CrestLoad(11, (unsigned long )0, (long long )1140850688);
  __CrestWorldSizeWithLimit((unsigned long )(& world_size), 16);
# 25 "hello.c"
  MPI_Comm_size(1140850688, & world_size);
  __CrestClearStack(12);
  __CrestLoad(13, (unsigned long )0, (long long )1140850688);
  __CrestRank((unsigned long )(& world_rank));
# 26 "hello.c"
  MPI_Comm_rank(1140850688, & world_rank);
  __CrestClearStack(14);
# 31 "hello.c"
  MPI_Get_processor_name(processor_name, & name_len);
  __CrestClearStack(15);
  __CrestLoad(16, (unsigned long )(& world_rank), (long long )world_rank);
  __CrestLoad(17, (unsigned long )(& world_size), (long long )world_size);
# 34 "hello.c"
  printf((char const * __restrict )"Hello world from processor %s, rank %d out of %d processors\n",
         processor_name, world_rank, world_size);
  __CrestClearStack(18);
  __CrestLoad(21, (unsigned long )0, (long long )1);
  __CrestLoad(20, (unsigned long )(& world_size), (long long )world_size);
  __CrestApply2(19, 12, (long long )(1 == world_size));
# 39 "hello.c"
  if (1 == world_size) {
    __CrestBranch(22, 3, 1);
    __CrestLoad(24, (unsigned long )(& world_size), (long long )world_size);
# 39 "hello.c"
    printf((char const * __restrict )"world size: %d\n", world_size);
    __CrestClearStack(25);
  } else {
    __CrestBranch(23, 4, 0);
    __CrestLoad(26, (unsigned long )(& world_size), (long long )world_size);
# 40 "hello.c"
    printf((char const * __restrict )"world size: %d\n", world_size);
    __CrestClearStack(27);
  }
  __CrestLoad(30, (unsigned long )0, (long long )1);
  __CrestLoad(29, (unsigned long )(& world_rank), (long long )world_rank);
  __CrestApply2(28, 16, (long long )(1 < world_rank));
# 43 "hello.c"
  if (1 < world_rank) {
    __CrestBranch(31, 6, 1);
# 43 "hello.c"
    printf((char const * __restrict )"a1:s\n");
    __CrestClearStack(33);
  } else {
    __CrestBranch(32, 7, 0);
# 44 "hello.c"
    printf((char const * __restrict )"a2:s\n");
    __CrestClearStack(34);
  }
  __CrestLoad(39, (unsigned long )0, (long long )2);
  __CrestLoad(38, (unsigned long )0, (long long )2);
  __CrestLoad(37, (unsigned long )(& a), (long long )a);
  __CrestApply2(36, 2, (long long )(2 * a));
  __CrestApply2(35, 12, (long long )(2 == 2 * a));
# 46 "hello.c"
  if (2 == 2 * a) {
    __CrestBranch(40, 9, 1);
# 46 "hello.c"
    printf((char const * __restrict )"b1:s\n");
    __CrestClearStack(42);
  } else {
    __CrestBranch(41, 10, 0);
# 47 "hello.c"
    printf((char const * __restrict )"b2:s\n");
    __CrestClearStack(43);
  }
# 49 "hello.c"
  fflush(stdout);
  __CrestClearStack(44);
# 51 "hello.c"
  MPI_Finalize();
  __CrestClearStack(45);
  __CrestLoad(46, (unsigned long )0, (long long )0);
  __CrestStore(47, (unsigned long )(& __retres9));
# 52 "hello.c"
  __retres9 = 0;
  __CrestLoad(48, (unsigned long )(& __retres9), (long long )__retres9);
  __CrestReturn(49);
# 5 "hello.c"
  return (__retres9);
}
}
void __globinit_hello(void)
{


  {
  __CrestInit();
}
}

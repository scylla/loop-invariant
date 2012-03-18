/*#include <assert.h>

void phase()
{
	int m=0;int a=10;
	while(m<=a)
	{
		//if(x%2==0)
			//m=a+1;
			m=m+1;
	}
	assert(m==11);
}*/
#include<stdlib.h>

//extern  __attribute__((__nothrow__)) void *malloc(size_t __size )  __attribute__((__malloc__)) ;
//line 451 "nxt-bad.c"
int create_msg(u_char *buf ) 
{ 
  u_char *p ;
  char *temp ;
  char *temp1 ;
  u_char *comp_dn ;
  u_char *comp_dn2 ;
  char exp_dn[200] ;
  char exp_dn2[200] ;
  u_char **dnptrs ;
  u_char **lastdnptr ;
  u_char **dnptrs2 ;
  int i ;
  int len ;
  int comp_size ;
  void *tmp ;
  void *tmp___0 ;
  void *tmp___1 ;
  void *tmp___2 ;
  void *tmp___3 ;
  size_t tmp___4 ;
  u_char *tmp___5 ;
  char *tmp___6 ;
  u_char **tmp___7 ;
  u_char **tmp___8 ;
  size_t tmp___9 ;
  u_char *tmp___10 ;
  u_char *tmp___11 ;
  register u_int16_t t_s ;
  register u_char *t_cp ;
  u_char *tmp___12 ;
  register u_int16_t t_s___0 ;
  register u_char *t_cp___0 ;
  u_char *tmp___13 ;
  register u_int32_t t_l ;
  register u_char *t_cp___1 ;
  u_char *tmp___14 ;
  u_char *tmp___15 ;
  u_char *tmp___16 ;
  register u_int16_t t_s___1 ;
  register u_char *t_cp___2 ;
  u_char *tmp___17 ;
  u_char **tmp___18 ;
  u_char **tmp___19 ;
  size_t tmp___20 ;
  u_char *tmp___21 ;
  u_char *tmp___22 ;
  register u_int32_t t_l___0 ;
  register u_char *t_cp___3 ;
  u_char *tmp___23 ;
  u_char *tmp___24 ;
  u_char *tmp___25 ;
  register u_int32_t t_l___1 ;
  register u_char *t_cp___4 ;
  u_char *tmp___26 ;
  u_char *tmp___27 ;
  u_char *tmp___28 ;
  register u_int32_t t_l___2 ;
  register u_char *t_cp___5 ;
  u_char *tmp___29 ;
  u_char *tmp___30 ;
  u_char *tmp___31 ;
  register u_int32_t t_l___3 ;
  register u_char *t_cp___6 ;
  u_char *tmp___32 ;
  u_char *tmp___33 ;
  u_char *tmp___34 ;

  {
#line 458
  len = 0;
#line 461
  tmp = malloc(2U * sizeof(unsigned char *));
#line 461
  dnptrs = (unsigned char **)tmp;
#line 462
  tmp___0 = malloc(2U * sizeof(unsigned char *));
#line 462
  dnptrs2 = (unsigned char **)tmp___0;
#line 464
  tmp___1 = malloc(200U * sizeof(unsigned char ));
#line 464
  comp_dn = (unsigned char *)tmp___1;
#line 465
  tmp___2 = malloc(200U * sizeof(unsigned char ));
#line 465
  comp_dn2 = (unsigned char *)tmp___2;
#line 467
  tmp___3 = malloc(400U * sizeof(char ));
#line 467
  temp1 = (char *)tmp___3;
#line 469
  temp = temp1;
#line 471
  p = buf;
#line 473
  strcpy((char * __restrict  )temp, (char const   * __restrict  )"HEADER JUNK:");
#line 475
  tmp___4 = strlen((char const   *)temp);
#line 475
  len = (int )((size_t )len + tmp___4);
#line 477
  while ((int )*temp != 0) {
#line 478
    tmp___5 = p;
#line 478
    p ++;
#line 478
    tmp___6 = temp;
#line 478
    temp ++;
#line 478
    *tmp___5 = (u_char )*tmp___6;
  }
#line 480
  strcpy((char * __restrict  )(exp_dn), (char const   * __restrict  )"lcs.mit.edu");
#line 482
  tmp___7 = dnptrs;
#line 482
  dnptrs ++;
#line 482
  *tmp___7 = (u_char *)(exp_dn);
#line 483
  tmp___8 = dnptrs;
#line 483
  dnptrs --;
#line 483
  *tmp___8 = (u_char *)((void *)0);
#line 485
  lastdnptr = (u_char **)((void *)0);
#line 487
  printf((char const   * __restrict  )"Calling dn_comp..\n");
#line 488
  comp_size = __dn_comp((char const   *)(exp_dn), comp_dn, 200, dnptrs, lastdnptr);
#line 489
  tmp___9 = strlen((char const   *)(exp_dn));
#line 489
  printf((char const   * __restrict  )"uncomp_size = %d\n", tmp___9);
#line 490
  printf((char const   * __restrict  )"comp_size = %d\n", comp_size);
#line 491
  printf((char const   * __restrict  )"exp_dn = %s, comp_dn = %s\n", exp_dn, (char *)comp_dn);
#line 493
  i = 0;
#line 493
  while (i < comp_size) {
#line 494
    tmp___10 = p;
#line 494
    p ++;
#line 494
    tmp___11 = comp_dn;
#line 494
    comp_dn ++;
#line 494
    *tmp___10 = *tmp___11;
#line 493
    i ++;
  }
#line 496
  len += comp_size;
  while (1) {
    t_s = (u_int16_t )30;
//#line 498
    t_cp = p;
    tmp___12 = t_cp;
    t_cp ++;
    *tmp___12 = (u_char )((int )t_s >> 8);
    *t_cp = (u_char )t_s;
    p += 2;
    break;
  }
#line 499
  p += 2;
#line 501
  while (1) {
#line 501
    t_s___0 = (u_int16_t )255;
#line 501
    t_cp___0 = p;
#line 501
    tmp___13 = t_cp___0;
#line 501
    t_cp___0 ++;
#line 501
    *tmp___13 = (u_char )((int )t_s___0 >> 8);
#line 501
    *t_cp___0 = (u_char )t_s___0;
#line 501
    p += 2;
#line 501
    break;
  }
#line 502
  p += 2;
#line 504
  while (1) {
#line 504
    t_l = (u_int32_t )255;
#line 504
    t_cp___1 = p;
#line 504
    tmp___14 = t_cp___1;
#line 504
    t_cp___1 ++;
#line 504
    *tmp___14 = (u_char )(t_l >> 24);
#line 504
    tmp___15 = t_cp___1;
#line 504
    t_cp___1 ++;
#line 504
    *tmp___15 = (u_char )(t_l >> 16);
#line 504
    tmp___16 = t_cp___1;
#line 504
    t_cp___1 ++;
#line 504
    *tmp___16 = (u_char )(t_l >> 8);
#line 504
    *t_cp___1 = (u_char )t_l;
#line 504
    p += 4;
#line 504
    break;
  }
#line 505
  p += 4;
#line 507
  while (1) {
#line 507
    t_s___1 = (u_int16_t )16;
#line 507
    t_cp___2 = p;
#line 507
    tmp___17 = t_cp___2;
#line 507
    t_cp___2 ++;
#line 507
    *tmp___17 = (u_char )((int )t_s___1 >> 8);
#line 507
    *t_cp___2 = (u_char )t_s___1;
#line 507
    p += 2;
#line 507
    break;
  }
#line 510
  p += 2;
#line 512
  len += 10;
#line 514
  strcpy((char * __restrict  )(exp_dn2), (char const   * __restrict  )"sls.lcs.mit.edu");
#line 516
  tmp___18 = dnptrs2;
#line 516
  dnptrs2 ++;
#line 516
  *tmp___18 = (u_char *)(exp_dn2);
#line 517
  tmp___19 = dnptrs2;
#line 517
  dnptrs2 --;
#line 517
  *tmp___19 = (u_char *)((void *)0);
#line 518
  lastdnptr = (u_char **)((void *)0);
#line 520
  printf((char const   * __restrict  )"Calling dn_comp..\n");
#line 521
  comp_size = __dn_comp((char const   *)(exp_dn2), comp_dn2, 200, dnptrs2, lastdnptr);
#line 522
  tmp___20 = strlen((char const   *)(exp_dn2));
#line 522
  printf((char const   * __restrict  )"uncomp_size = %d\n", tmp___20);
#line 523
  printf((char const   * __restrict  )"comp_size = %d\n", comp_size);
#line 524
  printf((char const   * __restrict  )"exp_dn2 = %s, comp_dn2 = %s\n", exp_dn2, (char *)comp_dn2);
#line 526
  len += comp_size;
#line 528
  i = 0;
#line 528
  while (i < comp_size) {
#line 529
    tmp___21 = p;
#line 529
    p ++;
#line 529
    tmp___22 = comp_dn2;
#line 529
    comp_dn2 ++;
#line 529
    *tmp___21 = *tmp___22;
#line 528
    i ++;
  }
#line 531
  while (1) {
#line 531
    t_l___0 = (u_int32_t )(1 << 24);
#line 531
    t_cp___3 = p;
#line 531
    tmp___23 = t_cp___3;
#line 531
    t_cp___3 ++;
#line 531
    *tmp___23 = (u_char )(t_l___0 >> 24);
#line 531
    tmp___24 = t_cp___3;
#line 531
    t_cp___3 ++;
#line 531
    *tmp___24 = (u_char )(t_l___0 >> 16);
#line 531
    tmp___25 = t_cp___3;
#line 531
    t_cp___3 ++;
#line 531
    *tmp___25 = (u_char )(t_l___0 >> 8);
#line 531
    *t_cp___3 = (u_char )t_l___0;
#line 531
    p += 4;
#line 531
    break;
  }
#line 532
  p += 4;
#line 533
  while (1) {
#line 533
    t_l___1 = (u_int32_t )0;
#line 533
    t_cp___4 = p;
#line 533
    tmp___26 = t_cp___4;
#line 533
    t_cp___4 ++;
#line 533
    *tmp___26 = (u_char )(t_l___1 >> 24);
#line 533
    tmp___27 = t_cp___4;
#line 533
    t_cp___4 ++;
#line 533
    *tmp___27 = (u_char )(t_l___1 >> 16);
#line 533
    tmp___28 = t_cp___4;
#line 533
    t_cp___4 ++;
#line 533
    *tmp___28 = (u_char )(t_l___1 >> 8);
#line 533
    *t_cp___4 = (u_char )t_l___1;
#line 533
    p += 4;
#line 533
    break;
  }
#line 534
  p += 4;
#line 535
  while (1) {
#line 535
    t_l___2 = (u_int32_t )0;
#line 535
    t_cp___5 = p;
#line 535
    tmp___29 = t_cp___5;
#line 535
    t_cp___5 ++;
#line 535
    *tmp___29 = (u_char )(t_l___2 >> 24);
#line 535
    tmp___30 = t_cp___5;
#line 535
    t_cp___5 ++;
#line 535
    *tmp___30 = (u_char )(t_l___2 >> 16);
#line 535
    tmp___31 = t_cp___5;
#line 535
    t_cp___5 ++;
#line 535
    *tmp___31 = (u_char )(t_l___2 >> 8);
#line 535
    *t_cp___5 = (u_char )t_l___2;
#line 535
    p += 4;
#line 535
    break;
  }
#line 536
  p += 4;
#line 537
  while (1) {
#line 537
    t_l___3 = (u_int32_t )0;
#line 537
    t_cp___6 = p;
#line 537
    tmp___32 = t_cp___6;
#line 537
    t_cp___6 ++;
#line 537
    *tmp___32 = (u_char )(t_l___3 >> 24);
#line 537
    tmp___33 = t_cp___6;
#line 537
    t_cp___6 ++;
#line 537
    *tmp___33 = (u_char )(t_l___3 >> 16);
#line 537
    tmp___34 = t_cp___6;
#line 537
    t_cp___6 ++;
#line 537
    *tmp___34 = (u_char )(t_l___3 >> 8);
#line 537
    *t_cp___6 = (u_char )t_l___3;
#line 537
    p += 4;
#line 537
    break;
  }
#line 538
  p += 4;
#line 540
  len += 16;
#line 542
  return (len);
}
}
void main()
{
	u_char *buf="abc";
	create_msg(buf);
}

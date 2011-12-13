#include<stdio.h>
/*@
	@ requires \valid_range((char*)s,0,n-1);
	@ ensures \forall integer i;0<=i<n ==> ((char*)s)[i]==c;
	*/
extern void memset(void *s,int c,size_t n);
#define LEN 20

void phase()
{
	int x=0,y=50;
	char buffer[LEN];
	while(x<100)
	{
		memset(buffer,0,LEN);
		x++;
		if(x>50)
			y++;
	}
	assert(y==100);//||x>0
}

#include<stdio.h>
/*@
	@ requires \valid_range((char*)s,0,n-1);
	@ ensures \forall integer i;0<=i<n ==> ((char*)s)[i]==c;
	*/
extern void memset(void *s,int c,size_t n);
#define LEN 20

int inc(int x)
{
	return x+1;
}

void phase()
{
	int i=0;
	i=i+1;
	if(i>0)
	{
		i=i+i;
	}
	while(i<10)
	{
		i=i+1;
		i=i-1;
		//i=inc(i);
	}
}
/*int x=0,y=50;
	char buffer[LEN];
	while(x<100)
	{
		memset(buffer,0,LEN);
		x++;
		if(x>50)
			y++;
	}
	assert(y==100);//||x>0*/

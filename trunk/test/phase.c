#include<stdio.h>

void phase()
{
	int x=0,y=50;
	while(x<100)
	{
		x++;
		if(x>50)
			y++;
	}
	assert(y==100);//||x>0
}

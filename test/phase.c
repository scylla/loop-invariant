#include<assert.h>

void phase()
{
	int x=0,y=50;
	while(x<100)
	{
		x=x+1;
		if(x>50)
			y=y+1;
	}
	assert(y==100);
}




void phase()
{
	int m=0;int a=10;
	/*@loop invariant (-1*m+-1*a)+16 ≡ 0;
	*/
	while(1==1)
	{
			m=m+1;			
			if(m>10)
			continue;
			m=m+2;
			if(m>20)
			continue;
	}
}


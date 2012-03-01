/*@
  @requires \valid_range(a,0,n-1);
  @requires \valid_range(b,0,n-1);
	
  @assigns \nothing;
	
  @behavior all_equal:
  @ assumes \forall int i; 0 <= i < n ==> a[i] == b[i];
  @ ensures \result == 1;
	
  @behavior some_not_equal:
  @  assumes \exists int i; 0 <= i < n && a[i] != b[i];
	@ ensures \result == 0;
	
	@complete behaviors all_equal, some_not_equal;
  @ disjoint behaviors all_equal, some_not_equal;
*/
int equal(int* a, int n, int* b)
{
	for (int i = 0; i < n; i++)
     if (a[i] != b[i])
       return 0;
	return 1;
}

void main()
{
	int a[]={1,2,3},b[]={1,2,4};
	int n=3;
	equal(a,n,b);
}

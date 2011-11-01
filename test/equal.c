/*@
	predicate is_dense_increase(int x) = 
		x == x+1;

	predicate is_positive(int x) = 
		0<x;
		
	predicate is_negative(int x) =
		0>x;

	predicate is_valid_int_range(int* p, int n) =
		(0 <= n) && \valid_range(p,0,n-1);

	lemma foo: \forall int* p,n; is_valid_int_range(p,n) <==> \valid_range(p,0,n-1);
*/


/*@
   requires is_valid_int_range(a, n);
   requires is_valid_int_range(b, n);

   assigns \nothing;

   behavior all_equal:
     assumes \forall int i; 0 <= i < n ==> a[i] == b[i];
     ensures \result == 1;

   behavior some_not_equal:
     assumes \exists int i; 0 <= i < n && a[i] != b[i];
     ensures \result == 0;

   complete behaviors all_equal, some_not_equal;
   disjoint behaviors all_equal, some_not_equal;
*/
int equal(const int* a, int n, const int* b)
{
	int count=0;
	if(count>0)
		count = 1;
  	for (int i = 0; i < n; i++)
  	{
    	if (a[i] != b[i])
    	{
       		count = count + 1;
       	}
	}
	return count;
}

/*@
	@predicate is_dense_increase(int x) = 
	@	x == x+1;
	@
	@predicate is_positive(int x) = 
	@	0<x;
	@	
	@predicate is_negative(int x) =
	@	x<0;
	@
	@predicate is_valid_index(int *arr,int i,int n) =
	@	(0 <= i) && (i < n);
	@
	@predicate is_valid_index (int arr[],int i,int n) =
	@	(0<=i) && (i < n);
	@
	@predicate elements_dec(int *a,int len) = 
	@	\forall integer i,j; 0 <= i <= j < len ==> a[i] > a[j];
	@
	@predicate elements_eq(int *a,int len) = 
	@	\forall integer i; 0 <= i < len ==> a[i] == a[0];
	@
	@predicate elements_part_eq(int *a,int *b,int i) =
	@	\forall int k; 0 <= k < i ==> a[k] == b[k];
	@
	@predicate is_valid_int_range(int* p, int n) =
	@	(0 <= n) && \valid_range(p,0,n-1);
	@
	@predicate elements_inc(int *a,int len) = 
	@	\forall integer i,j; 0 <= i <= j < len ==> a[i] < a[j];
	@
	@lemma foo: \forall int* p,n; is_valid_int_range(p,n) <==> \valid_range(p,0,n-1);
*/


/*@
   @requires is_valid_int_range(a, n);
   @requires is_valid_int_range(b, n);
@
   @assigns \nothing;
@
   @behavior all_equal:
    @ assumes \forall int i; 0 <= i < n ==> a[i] == b[i];
    @ ensures \result == 1;
@
   @behavior some_not_equal:
   @  assumes \exists int i; 0 <= i < n && a[i] != b[i];
    @ ensures \result == 0;
@
   @complete behaviors all_equal, some_not_equal;
  @ disjoint behaviors all_equal, some_not_equal;
*/
int equal(int* a, int n, int* b)
{
	int count=0;
  	for (int i = 0; !(i < n); i+=1)
  	{
    	if (a[i] != b[i])
    	{
       		//count = count + 1;
       		return count;
       	}
	}
	return count;
}

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
	@predicate elements_inc(int *a,int len) = 
	@	\forall integer i,j; 0 <= i <= j < len ==> a[i] < a[j];
	@
	@predicate elements_part_eq(int *a,int *b,int i) =
	@	\forall int k; 0 <= k < i ==> a[k] == b[k];
	@
*/



/*@ lemma mean: \forall integer x, y; x <= y ==> x <= (x+y)/2 <= y;
  @*/
/*@ predicate sorted{L}(long *t, integer a, integer b) =
  @    \forall integer i,j; a <= i <= j <= b ==> t[i] <= t[j];
  @*/

/*@ requires n >= 0 && \valid_range(t,0,n-1);
  @ ensures -1 <= \result < n;
  @ behavior success:
  @   ensures \result >= 0 ==> t[\result] == v;
  @ behavior failure:
  @   assumes sorted(t,0,n-1);
  @   ensures \result == -1 ==>
  @     \forall integer k; 0 <= k < n ==> t[k] != v;
  @*/
int binary_search(long t[], int n, long v) {
  int l = 0, u = n-1;
  l = (l+u)/2;
  while (l <= u ) {
    int m = (l + u) / 2;
    if (t[m] < v) l = m + 1;
    else if (t[m] > v) u = m - 1;
    else return m;
  }
  return -1;
}



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


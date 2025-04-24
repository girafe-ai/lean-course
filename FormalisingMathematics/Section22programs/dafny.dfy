// Язык Dafny

method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures 0 <= x ==> y == x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  assert v == 3;
}

method SumTo(n: nat) returns (sum: nat)
  ensures sum == n * (n + 1) / 2
{
  var i := 0;
  sum := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant sum == i * (i - 1) / 2
  {
    sum := sum + i;
    i := i + 1;
  }
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= index < a.Length ==> a[index] == key
  ensures (exists i :: 0 <= i < a.Length && a[i] == key) <==> (0 <= index < a.Length)
{
  var lo := 0;
  var hi := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] > key
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
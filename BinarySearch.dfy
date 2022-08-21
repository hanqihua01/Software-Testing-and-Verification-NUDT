method BinarySearch(a: array<int>, key: int) returns (index: int)
requires a.Length > 0 && forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
ensures index >= 0 ==> 0 <= index < a.Length && a[index] == key
{
  var l := 0;
  var r := a.Length;
  while (l < r)
  invariant 0 <= l <= r <= a.Length
  invariant forall i :: 0 <= i < a.Length && !(l <= i < r) ==> a[i] != key;
  {
    var c := (l + r) / 2;
    if (a[c] < key) { l := c + 1; }
    else if (key < a[c]) { r := c; } 
    else { return c; }
  }
  return -1;
}
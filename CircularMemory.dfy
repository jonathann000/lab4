// class CircularMemory
// This class implements a cicular buffer with 2 int typed pointers

/*
Authors: Adam Williams, Jonathan Naumanen, Alexander Stenström
Group: 15
*/
class CircularMemory
{
  var cells : array<int>;
  var read_position : int;
  var write_position : int;
  var isFlipped : bool;

  constructor Init(cap : int)
    requires cap > 0
    ensures cap == cells.Length
    ensures read_position == 0
    ensures write_position == 0
    ensures isFlipped == false
  {
    cells := new int[cap];
    read_position, write_position := 0, 0;
    isFlipped := false;
  }

  predicate Valid() 
    reads this
  {
    // array can't be less than 1
    0 < cells.Length &&
    //write position needs to be inside index boundaries
    0 <= write_position < cells.Length && 
    //same with read position
    0 <= read_position < cells.Length && 
    //if the array is flipped, the write position needs to be greater than the read position
    (isFlipped ==> write_position <= read_position) && 
    //if the array is not flipped, the write position needs to be less than the read position
    (!isFlipped ==> write_position >= read_position)
  }

  predicate isEmpty()
    reads this
  {
    read_position == write_position && !isFlipped
  }

  predicate isFull()
    reads this
  {
    read_position == write_position && isFlipped
  }

  method Read() returns (isSuccess : bool, content : int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures  isSuccess ==> content == old(cells[(read_position)])
    ensures !isSuccess ==> content == 0
    ensures !isSuccess ==> read_position == old(read_position)
    ensures cells.Length == old(cells.Length)
  {
    if(isFlipped) //om flipped write kan inte gå förbi read om !flipped read kan inte gå förbi write
    {
      isSuccess := true;
      content := cells[read_position];
      read_position := read_position + 1;
      if(read_position == cells.Length){
        isFlipped := false;
        read_position := 0;
      }
    }
    else // not flipped
    {
      if(read_position == write_position){
        isSuccess := false;
        content := 0;
      } 
      else {
      isSuccess := true;
      content := cells[read_position];
      read_position := read_position + 1;
      }
    }
  }

  method Write(input : int) returns (isSuccess : bool)
    modifies cells, `write_position, `isFlipped
    requires Valid()
    ensures Valid() 
    ensures  isSuccess ==> cells[old(write_position)] == input
    ensures !isSuccess ==> cells[(write_position)] == old(cells[(write_position)])
    ensures !isSuccess ==> write_position == old(write_position)
    ensures cells.Length == old(cells.Length)
  {
    if(!isFlipped)
    {
      isSuccess := true;
      cells[write_position] := input; 
      write_position := (write_position + 1);
      if(write_position == cells.Length){
        write_position := 0;
        isFlipped := true;
      }
    }
    else // flipped
    {
      if(write_position == read_position){
        isSuccess := false;
      } 
      else {
      isSuccess := true;
      cells[write_position] := input; 
      write_position := (write_position + 1);
      }
    }

  }

  // Method to create an array of zeroes
  method createArrayOfZeroes (length : int) returns (arrayOfZeroes : array<int>)
    requires length > 0
    ensures arrayOfZeroes.Length == length
    ensures forall j : nat :: 0 <= j < length ==> arrayOfZeroes[j] == 0
    ensures fresh(arrayOfZeroes)
  {
    arrayOfZeroes := new int[length];
    var i := 0;
    while (i < length)
    modifies arrayOfZeroes
    decreases length - i
    invariant 0 <= i <= length
    invariant forall j : nat :: 0 <= j < i ==> arrayOfZeroes[j] == 0
    {
      arrayOfZeroes[i] := 0;
      i := i + 1;
    }
  }

  method DoubleCapacity()
    modifies this
    requires cells.Length > 0
    requires cells.Length < 2147483647 / 2
    requires Valid()
    ensures Valid()
    ensures cells.Length == 2 * old(cells.Length)
    ensures read_position == old(read_position)
    ensures write_position == old(write_position)
    ensures cells.Length > old(cells.Length)
    ensures forall j : nat :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j]) // alla gamla värden finns kvar i nya arrayen
    ensures forall j : nat :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0 // alla nya värden är 0
    
  {
    // save old values
    var oldArrayLength := cells.Length;
    var oldArray := cells;
    // create new array with double capacity
    cells := createArrayOfZeroes(cells.Length * 2);
    var i := 0;
    
    while (i < oldArrayLength)
    modifies cells
    decreases oldArrayLength - i
    invariant 0 <= i < oldArrayLength
    invariant forall j : nat :: oldArrayLength <= j < cells.Length ==> cells[j] == 0
    invariant forall j : nat :: 0 <= j < i ==> cells[j] == old(cells[j])
    {
      cells[i] := oldArray[i];
      if (i == oldArrayLength - 1){
        break;
      }else{
        i := i + 1;
      }
    }
  }
}

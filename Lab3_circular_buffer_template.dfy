// class CircularMemory
// This class implements a cicular buffer with with 2 int typed pointers

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

 /* predicate isEmpty()
    reads this
  {
    read_position == write_position && !isFlipped
  }

  predicate isFull()
    reads this
  {
    read_position == write_position && isFlipped
  }
*/
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
  // Question 3 for Lab 4
  method DoubleCapacity()
    modifies this;
    requires cells.Length > 0
    requires cells.Length < 2147483647 / 2
    requires Valid()
    ensures Valid()
    ensures cells.Length == 2 * old(cells.Length)
    ensures read_position == old(read_position)
    ensures write_position == old(write_position)
    ensures forall j : int :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j])
    ensures forall j : int :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0
    
  {
    // one or more loops to double the capacity of cells
    // the most important part is the loop invariants!
    // initialize new circular memory with double capacity
    var newCells : array<int> := new int[2 * cells.Length];

    var i := 0;

    while(i < cells.Length)
      invariant newCells.Length == 2 * old(cells.Length)
      invariant forall j : nat :: 0 <= j <= i ==> newCells.Length > j
      invariant 0 <= i <= cells.Length
      invariant forall j : nat :: 0 <= j < i ==> newCells[j] == cells[j]
      invariant forall j : int :: i <= j < newCells.Length ==> newCells[j] == 0
      invariant forall j : int :: cells.Length <= j < newCells.Length ==> newCells[j] == 0
      //invariant 0 <= j <= cells.Length;  
      invariant cells.Length == old(cells.Length)
      invariant read_position == old(read_position)
      invariant write_position == old(write_position)
      invariant forall j : int :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j])
      invariant forall j : int :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0
    {
      newCells[i] := cells[i];
      i := i + 1;

    }
    cells := newCells;
    

  }
}

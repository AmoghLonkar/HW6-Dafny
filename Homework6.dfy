datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{

	match tree
    case Leaf => Nil
    case Node(leftTree, rightTree, root) => append(flatten(leftTree), Cons(root, flatten(rightTree)))
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
{
	match xs
    case Nil => ys
    case Cons(x, xs') => Cons(x, append(xs', ys))
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match tree
    case Leaf => false
    case Node(leftTree, rightTree, root) => treeContains(leftTree, element) || treeContains(rightTree, element)
}

function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x, xs') => (x == element) || listContains(xs', element)
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	
}
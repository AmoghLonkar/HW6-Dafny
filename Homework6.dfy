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
    case Node(leftTree, rightTree, root) => (root == element) || treeContains(leftTree, element) || treeContains(rightTree, element)
}

function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(x, xs') => (x == element) || listContains(xs', element)
}

//Based on memberOfAppend from 12May20 lecture example
ghost method memberOfList<T>(xs:List<T>, ys:List<T>, element: T)
ensures ( listContains(xs, element)  ||  listContains(ys, element) ) <==> listContains(append(xs,ys), element)
{
    match xs
    case Nil => {}
    case Cons(x,xs') => {
        // memberOfAppend(e,xs',ys);  // <-- use the inductive hypothesis
        // Dafny knows post-condition
        // member(e,append(xs',ys)) == ( member(e,xs')  ||  member(e,ys) )
        /*assert member(e,append(xs,ys))
            == member(e,append(Cons(x,xs'),ys))
            == member(e,Cons(x,append(xs',ys)))
            == (e==x) || member(e,append(xs',ys))
            == (e==x) || member(e,xs') || member(e,ys)
            == member(e, Cons(x,xs'))  || member(e,ys)
            == member(e, xs)           || member(e,ys)
            ;*/
        calc {
            listContains(append(xs,ys), element);
            == listContains(append(Cons(x,xs'),ys), element);
            == listContains(Cons(x,append(xs',ys)), element);
            == (element == x) || listContains(append(xs',ys), element);
            == { memberOfList(xs',ys, element); }
               (element == x) || listContains(xs', element) || listContains(ys, element);
            == listContains(Cons(x,xs'), element)  || listContains(ys, element);
            == listContains(xs, element)           || listContains(ys, element);
        }
    }
}

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	match tree
    case Leaf => {}
    case Node(leftTree, rightTree, root) => {
        calc{
                treeContains(tree, element);
            == treeContains(Node(leftTree, rightTree, root), element);
            == (root == element) || treeContains(leftTree, element) || treeContains(rightTree, element);
            == treeContains(leftTree, element) || listContains(Cons(root, flatten(rightTree)), element);
            == listContains(flatten(leftTree), element) || listContains(Cons(root, flatten(rightTree)), element);
            == { memberOfList(flatten(leftTree), Cons(root, flatten(rightTree)), element); }
               listContains(append(flatten(leftTree), Cons(root, flatten(rightTree))), element);
            == listContains(flatten(Node(leftTree, rightTree, root)), element);
            == listContains(flatten(tree), element);
        } 
    }
}
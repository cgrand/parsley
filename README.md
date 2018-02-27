If anyone stumbles here trying to find an incremental parser, here is the 1998 paper ([Efficient and Flexible Incremental Parsing](https://www.researchgate.net/profile/SL_Graham/publication/2377179_Efficient_and_Flexible_Incremental_Parsing/links/004635294e13f23ef1000000/Efficient-and-Flexible-Incremental-Parsing.pdf
)) that I should have found before embarking in this failed (expectations not met) project.

# Parsley 

## Parsnip

Parsley has been a test bed and a proof of concept for total incremental parsers. However it suffers from severe limitations (mainly revolving around lookaheads, both at the lexeme and production level) which hinder further development and acceptance.

Further development of the concepts and techniques explored in Parsley will occur in [Parsnip](https://github.com/cgrand/parsnip/).

## Introduction

Parsley generates *total and truly incremental parsers*.

Total: a Parsley parser *yields a parse-tree for any input string*.

Truly incremental: a Parsley parser can operate as a text buffer, in best cases
recomputing the parse-tree after a sequence of edits happens in *logarithmic 
time* (worst case: it behaves like a restartable parser).

Parsley parsers have *no separate lexer*, this allows for better compositionality
of grammars. 

For now Parsley uses the same technique (for lexer-less parsing) as described
in this paper: 
Context-Aware Scanning for Parsing Extensible Languages
http://www.umsec.umn.edu/publications/Context-Aware-Scanning-Parsing-Extensible-Language

(I independently rediscovered this technique and dubbed it LR+.)

Without a separate lexer, a language is entirely defined by its grammar.
A grammar is an alternation of keywords (non-terminal names) and other values.
A keyword and another value form a production rule.


## Specifying grammars

A simple grammar is:

    :expr #{"x" ["(" :expr* ")"]}

`x` `()` `(xx)` `((x)())` are recognized by this grammar.

By default the main production of a grammar is the first one.

A production right value is a combination of:

* strings and regexes (terminals -- the set of terminal types is broader and
  even open, more later)
* keywords (non-terminals) which can be suffixed by `*`, `+` or `?` to denote 
  repetitions or options.
* sets to denote an alternative
* vectors to denote a sequence. Inside vectors `:*`, `:+` and `:?` are postfix unary
  operators. That is `["ab" :+]` denotes a non-empty repetition of the `ab` 
  string

A production left value is always a keyword. If this keyword is suffixed by `-`,
no node will be generated in the parse-tree for this rule, its child nodes are
inlined in the parent node. Rules with such names are called anonymous rules.
An anonymous rule must be referred to by its base name (without the `-`).

These two grammars specify the same language but the resulting parse-trees will
be different (additional `:expr-rep` nodes):

    :expr #{"x" ["(" :expr* ")"]}

    :expr #{"x" :expr-rep}
    :expr-rep ["(" :expr* ")"]

These two grammars specify the same language and the same parse-trees:

    :expr #{"x" ["(" :expr* ")"]}

    :expr #{"x" :expr-rep}
    :expr-rep- ["(" :expr* ")"]

## Creating parsers

A parser is created using the `parser` or `make-parser` functions.

    (require '[net.cgrand.parsley :as p])
    (def p (p/parser :expr #{"x" ["(" :expr* ")"]}))
    (pprint (p "(x(x))"))
    
    {:tag :net.cgrand.parsley/root,
     :content
       [{:tag :expr,
         :content
           ["("
            {:tag :expr, :content ["x"]}
            {:tag :expr, :content ["(" {:tag :expr, :content ["x"]} ")"]}
            ")"]}]}
    
    ; running on malformed input with garbage
    (pprint (p "a(zldxn(dez)"))
    
    {:tag :net.cgrand.parsley/unfinished,
     :content
       [{:tag :net.cgrand.parsley/unexpected, :content ["a"]}
        {:tag :net.cgrand.parsley/unfinished,
         :content
           ["("
            {:tag :net.cgrand.parsley/unexpected, :content ["zld"]}
            {:tag :expr, :content ["x"]}
            {:tag :net.cgrand.parsley/unexpected, :content ["n"]}
            {:tag :expr,
             :content
               ["("
                {:tag :net.cgrand.parsley/unexpected, :content ["dez"]}
                ")"]}]}]}

 
## Creating buffers

Creating a buffer, editing it and getting its resulting parse-tree:

    (-> p p/incremental-buffer (p/edit 0 0 "(") (p/edit 1 0 "(x)") p/parse-tree pprint)
    
    {:tag :net.cgrand.parsley/unfinished,
     :content
       [{:tag :net.cgrand.parsley/unfinished,
         :content
           ["("
            {:tag :expr, :content ["(" {:tag :expr, :content ["x"]} ")"]}]}]}

Incremental parsing at work:
  
    => (def p (p/parser :expr #{"x" "\n" ["(" :expr* ")"]}))
    #'net.cgrand.parsley/p
    => (let [line (apply str "\n" (repeat 10 "((x))"))
             input (str "(" (apply str (repeat 1000 line)) ")")
             buf (p/incremental-buffer p)
             buf (p/edit buf 0 0 input)]
         (time (p/parse-tree buf))
         (time (p/parse-tree (-> buf (p/edit 2 0 "(") (p/edit 51002 0 ")"))))
         nil)
    "Elapsed time: 508.834 msecs"
    "Elapsed time: 86.038 msecs"
    nil

Hence, *reparsing the buffer only took a fraction of the original time* despite
the buffer having been modified at the start and at the end.

## Incremental parsing 

The input string is split into _chunks_ (lines by default) and chunks are always
reparsed as a whole, so don't experiment with incremental parsing with 1-line
inputs!

Let's look at a bit more complex example:

    => (def p (p/parser {:main :expr*
                         :space :ws?
                         :make-node (fn [tag content] {:tag tag :content content :id (gensym)})}
                :ws #"\s+"
                :expr #{#"\w+" ["(" :expr* ")"]}))

This example introduces the option map: if the first arg to `parser` is a map 
(instead of a keyword), it's a map of options. See Options for more.

The important option here is that we redefine how nodes of the parse-tree are
constructed (via the `make-node` option). We add a unique identifier to each
node.

Now let's create a 3-line input and parse it: 

    => (def buf (-> p incremental-buffer (edit 0 0 "((a)\n(b)\n(c))")))
    => (-> buf parse-tree pprint)
    nil
    {:tag :net.cgrand.parsley/root,
     :content
       [{:tag :expr,
         :content
           ["("
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["a"], :id G__1806} ")"],
             :id G__1807}
            {:tag :ws, :content ["\n"], :id G__1808}
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["b"], :id G__1809} ")"],
             :id G__1810}
            {:tag :ws, :content ["\n"], :id G__1811}
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["c"], :id G__1812} ")"],
             :id G__1813}
            ")"],
         :id G__1814}],
     :id G__1815}

Now, let's modify this "B" in "BOO" and parse the buffer again:

    => (-> buf (edit 6 1 "BOO") parse-tree pprint)
    nil
    {:tag :net.cgrand.parsley/root,
     :content
       [{:tag :expr,
         :content
           ["("
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["a"], :id G__1806} ")"],
             :id G__1807}
            {:tag :ws, :content ["\n"], :id G__1818}
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["BOO"], :id G__1819} ")"],
             :id G__1820}
            {:tag :ws, :content ["\n"], :id G__1811}
            {:tag :expr,
             :content ["(" {:tag :expr, :content ["c"], :id G__1812} ")"],
             :id G__1813}
            ")"],
         :id G__1821}],
     :id G__1822}
-----

We can spot that 5 out of the 10 nodes are shared with the previous parse-tree.


## Options

`:main` specifies the root production, by default this is the the first 
production of the grammar.

`:root-tag` specifies the tag name to use for the root node 
(`:net.cgrand.parsley/root` by default).

`:space` specifies a production which will be interspersed between every symbol
(terminal or not) *except in a sequence created with `unspaced`.* 

`:make-node` specifies a function whose arglist is `[tag children-vec]` which
returns a new node. By default create instances the Node record with keys `tag`
and `content`.

`:make-unexpected` specifies a 1-arg function which converts a string (of 
unexpected characters) to a node. By defaut delegates to `:make-node`.

`:make-leaf` specifies a 1-arg function which converts a string (token) to a
node, by default behaves like identity.

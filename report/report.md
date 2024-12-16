---
title: Report for the _proof assistant project_
author: Vladimir Kukharenko
---

This is an example for the report in _Markdown_ format, which is a text format that can be converted to anything including pdf. I am fine with any other tool to produce the pdf though (Word, LaTeX, etc.). You can see the syntax at <https://pandoc.org/MANUAL.html>.

In order to produce the pdf, you should install `pandoc`, on Ubuntu this can be done with

```
sudo apt install pandoc
```

and then you can compile it to pdf by typing

```
pandoc report.md -o report.pdf
```

or simply

```
make
```

Erase the above and write an introduction.

# What was implemented in the project

Explain. You can write inline code `let x = 4`{.ocaml} or cite paragraphs of your code

```ocaml
let rec f x =
  let y = x + x in
  y * y
```

you have words in _italic_ or in **bold**.

## Simple types

Everything was implemented, all first 3 tasks.

Optional task 4 was skipped.

## Dependent types

Everything was implemented from 5.1 to 5.14 (ii).

I had a really hard time with equalities. I could make other proofs, but I really need to spend more time on equality types.

# Difficulties encountered

A little bit repetitive (it is ok for programming in general). So to speed up things a little bit some codegen was used (to generate errors and some repetitive parts, for example).

Interactivity for dependent types is quite complicated. Seems like it is not explicit enough.

# Implementation choices

In all cases, a minimum of possible variables was used.

The variable names didn't fit into parser.mly choice, so I had to change it.

# Possible extensions

Imagine.

# Conclusion

It was a really interesting task. Now I understand those topics better.
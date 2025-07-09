#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *
#show: show-theorion

#let vdash = math.class("normal", math.tack.r)
#let Vdash = math.class("normal", math.tack.r.double)

#show: rest => book(title: [公理集合论], 
authors: "Aki Sakuchan", 
bib-file: "references.bib",
rest)

#include "命题逻辑.typ"

#include "一阶逻辑.typ"

#include "公理集合论.typ"

#include "宇宙.typ"
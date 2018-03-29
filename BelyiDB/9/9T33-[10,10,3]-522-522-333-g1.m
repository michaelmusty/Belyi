s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[10,10,3]-522-522-333-g1";
s`BelyiDBFilename := "9T33-[10,10,3]-522-522-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 10, 10, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 9, 5, 7, 6, 2, 4, 8, 1, 3 ],
[ 2, 8, 5, 9, 6, 3, 4, 1, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 9, 4, 8, 2, 6, 5, 1, 7, 3 ],
[ 6, 7, 4, 9, 2, 8, 5, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
\[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 3, 4, 6, 9, 8, 1, 2, 5 ],
[ 9, 7, 8, 2, 3, 1, 4, 5, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 4, 6, 9, 5, 3, 2, 8, 7, 1 ],
[ 4, 9, 6, 5, 1, 8, 2, 3, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 9, 5, 7, 6, 2, 4, 8, 1, 3 ],
[ 2, 8, 5, 9, 6, 3, 4, 1, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 9, 4, 8, 2, 6, 5, 1, 7, 3 ],
[ 6, 7, 4, 9, 2, 8, 5, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 3, 4, 6, 9, 8, 1, 2, 5 ],
[ 9, 7, 8, 2, 3, 1, 4, 5, 6 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;

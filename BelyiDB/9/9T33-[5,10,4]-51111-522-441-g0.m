s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[5,10,4]-51111-522-441-g0";
s`BelyiDBFilename := "9T33-[5,10,4]-51111-522-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 5, 10, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 2, 7, 4, 3, 6, 5, 8, 9, 1 ],
[ 6, 9, 1, 4, 3, 5, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 7, 6, 4, 3, 1, 2, 8, 9, 5 ],
[ 9, 5, 6, 4, 3, 2, 1, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 2, 1, 7, 9, 6, 3, 8, 5, 4 ],
[ 8, 2, 1, 6, 9, 5, 3, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
\[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 6, 7, 8, 9 ],
[ 6, 9, 7, 3, 8, 4, 1, 5, 2 ],
[ 8, 7, 9, 4, 6, 1, 3, 5, 2 ]
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
[ 7, 2, 3, 4, 5, 8, 9, 1, 6 ],
[ 4, 8, 2, 3, 6, 5, 9, 1, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 8, 9, 4, 5, 6, 7, 1, 2 ],
[ 4, 8, 9, 1, 2, 5, 6, 7, 3 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 2, 6, 4, 5, 8, 7, 9, 1 ],
[ 4, 9, 2, 1, 6, 5, 3, 7, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 3, 2, 6, 4, 1, 9, 7, 8, 5 ],
[ 4, 5, 2, 1, 8, 9, 3, 7, 6 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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

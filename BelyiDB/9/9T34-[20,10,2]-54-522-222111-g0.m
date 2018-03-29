s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[20,10,2]-54-522-222111-g0";
s`BelyiDBFilename := "9T34-[20,10,2]-54-522-222111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 20, 10, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 2, 1, 5, 6, 4, 7, 3, 9, 8 ],
[ 3, 2, 1, 7, 5, 8, 4, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 2, 1, 5, 3, 6, 7, 4, 9, 8 ],
[ 3, 2, 1, 4, 7, 8, 5, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ],
[ 6, 9, 5, 4, 3, 1, 7, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
\[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
\[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 9, 1, 2, 7, 6, 5, 4, 3, 8 ],
[ 6, 2, 3, 8, 7, 1, 5, 4, 9 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 4, 5, 3, 1, 8, 6, 9, 7 ],
[ 8, 4, 1, 2, 3, 7, 6, 9, 5 ],
[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 5, 3, 2, 8, 6, 9, 7 ],
[ 8, 4, 5, 1, 3, 7, 6, 9, 2 ],
[ 9, 3, 2, 4, 5, 6, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 8, 4, 1, 6, 7, 9, 3, 5 ],
[ 7, 8, 1, 9, 3, 5, 6, 2, 4 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 6, 7, 9, 5, 8, 2, 3 ],
[ 5, 9, 8, 6, 1, 3, 4, 7, 2 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]
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

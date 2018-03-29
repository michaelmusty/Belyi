s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,20,2]-63-54-22221-g1";
s`BelyiDBFilename := "9T34-[6,20,2]-63-54-22221-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 20, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 7, 5, 6, 9, 2, 4, 1, 8 ],
[ 4, 8, 6, 1, 7, 3, 5, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 7, 4, 6, 2, 8, 9, 1, 5 ],
[ 4, 8, 5, 1, 3, 9, 7, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 2, 8, 6, 9, 7, 5, 3, 4, 1 ],
[ 3, 9, 1, 7, 8, 6, 4, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
\[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 7, 4, 8, 2, 5, 6, 1, 3 ],
[ 7, 8, 5, 9, 3, 6, 1, 2, 4 ]
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
[ 4, 1, 5, 3, 6, 2, 8, 9, 7 ],
[ 8, 4, 6, 3, 1, 9, 5, 7, 2 ],
[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 3, 9, 7, 4, 1, 6, 5, 2 ],
[ 9, 6, 5, 2, 7, 8, 1, 4, 3 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 5, 2, 6, 7, 8, 9, 4, 1 ],
[ 3, 9, 8, 1, 4, 2, 6, 5, 7 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 1, 6, 2, 7, 4, 3, 8 ],
[ 5, 3, 7, 8, 4, 1, 9, 6, 2 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
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

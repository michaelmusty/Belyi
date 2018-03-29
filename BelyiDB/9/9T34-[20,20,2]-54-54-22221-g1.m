s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[20,20,2]-54-54-22221-g1";
s`BelyiDBFilename := "9T34-[20,20,2]-54-54-22221-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 20, 20, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 3, 8, 2, 5, 6, 7, 4, 9, 1 ],
[ 4, 9, 3, 1, 7, 8, 5, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 5, 8, 4, 6, 2, 7, 3, 9, 1 ],
[ 1, 9, 5, 7, 3, 8, 4, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 3, 7, 9, 5, 6, 2, 4, 1, 8 ],
[ 4, 8, 6, 1, 7, 3, 5, 2, 9 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
\[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 7, 8, 9, 6, 4, 2, 3, 5, 1 ],
[ 8, 9, 6, 7, 5, 3, 4, 1, 2 ]
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
[ 5, 3, 8, 6, 4, 7, 1, 9, 2 ],
[ 9, 7, 5, 2, 4, 1, 3, 6, 8 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 5, 7, 2, 9, 8, 6, 3, 1 ],
[ 4, 9, 1, 8, 7, 2, 6, 3, 5 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 9, 2, 6, 4, 7, 5, 1, 8 ],
[ 3, 8, 5, 1, 4, 7, 9, 6, 2 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 6, 5, 7, 9, 2, 1, 8 ],
[ 7, 8, 2, 1, 3, 4, 9, 5, 6 ],
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,20,5]-6111-54-51111-g0";
s`BelyiDBFilename := "9T34-[6,20,5]-6111-54-51111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 20, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 2, 9, 4, 5, 8, 3, 1 ],
[ 1, 9, 3, 8, 5, 6, 2, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 2, 3, 8, 5, 4, 9, 1 ],
[ 1, 9, 3, 4, 7, 6, 2, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
\[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 5, 2, 3, 4, 7, 8, 9, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ]
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
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 1, 3, 4, 5, 8, 9, 2 ],
[ 1, 3, 9, 4, 5, 6, 2, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 2, 9, 4, 5, 8, 3, 1 ],
[ 1, 9, 3, 8, 5, 6, 2, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 2, 3, 8, 5, 4, 9, 1 ],
[ 1, 9, 3, 4, 7, 6, 2, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 5, 2, 3, 4, 7, 8, 9, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 7, 8 ]
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

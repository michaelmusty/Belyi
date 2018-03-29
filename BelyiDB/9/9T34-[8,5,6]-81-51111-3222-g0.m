s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,5,6]-81-51111-3222-g0";
s`BelyiDBFilename := "9T34-[8,5,6]-81-51111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 5, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 9, 2, 1, 4, 5, 3, 7, 6, 8 ],
[ 9, 3, 2, 6, 4, 5, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 9, 2, 1, 4, 3, 6, 7, 5, 8 ],
[ 9, 3, 2, 5, 4, 8, 6, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 6, 2, 1, 4, 3, 9, 7, 8, 5 ],
[ 8, 3, 2, 5, 4, 9, 1, 7, 6 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
\[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 1, 9, 3, 2, 5, 4, 7, 6, 8 ],
[ 9, 1, 4, 3, 6, 5, 8, 7, 2 ]
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
[ 3, 4, 2, 5, 6, 7, 8, 1, 9 ],
[ 1, 8, 3, 4, 2, 6, 5, 9, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 5, 6, 8, 7, 9, 1 ],
[ 1, 9, 3, 4, 2, 7, 5, 8, 6 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 6, 5, 7, 8, 9, 1 ],
[ 1, 9, 3, 5, 2, 6, 4, 8, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 2, 4, 5, 6, 7, 8, 9, 1 ],
[ 1, 9, 2, 4, 3, 6, 5, 8, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
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

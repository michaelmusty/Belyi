s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,12,6]-6111-432-3222-g0";
s`BelyiDBFilename := "9T34-[6,12,6]-6111-432-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 12, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 4, 9, 8, 2, 6, 7, 5, 3, 1 ],
[ 5, 9, 4, 8, 1, 7, 6, 3, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 2, 9, 6, 5, 7, 3, 8, 4, 1 ],
[ 3, 9, 1, 6, 8, 4, 5, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
\[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 2, 9, 6, 7, 8, 3, 5, 4, 1 ],
[ 3, 9, 1, 6, 8, 7, 4, 5, 2 ]
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
[ 9, 3, 7, 1, 8, 4, 2, 5, 6 ],
[ 9, 4, 7, 2, 6, 8, 3, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 8, 9, 1, 5, 7, 3, 4, 6, 2 ],
[ 8, 3, 9, 6, 7, 4, 5, 1, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 2, 9, 6, 5, 7, 3, 8, 4, 1 ],
[ 3, 9, 1, 6, 8, 4, 5, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 2, 9, 6, 7, 8, 3, 5, 4, 1 ],
[ 3, 9, 1, 6, 8, 7, 4, 5, 2 ]
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

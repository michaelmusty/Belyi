s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[20,3,6]-54-33111-3222-g0";
s`BelyiDBFilename := "9T34-[20,3,6]-54-33111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 20, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 1, 6, 3, 2, 9, 4, 5, 8, 7 ],
[ 7, 1, 4, 3, 6, 5, 2, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 6, 2, 3, 1, 9, 4, 5, 8, 7 ],
[ 7, 4, 2, 3, 6, 5, 1, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
\[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
\[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 1, 5, 3, 9, 6, 2, 4, 8, 7 ],
[ 2, 1, 6, 3, 7, 4, 5, 9, 8 ]
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
[ 2, 6, 9, 1, 4, 5, 8, 3, 7 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 5, 9, 1, 4, 8, 2, 3, 6 ],
[ 8, 3, 4, 2, 5, 6, 7, 9, 1 ],
[ 3, 7, 1, 5, 4, 8, 9, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 7, 2, 9, 6, 4, 1, 3, 5 ],
[ 2, 9, 4, 5, 3, 6, 7, 8, 1 ],
[ 7, 5, 8, 6, 2, 4, 1, 9, 3 ]
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

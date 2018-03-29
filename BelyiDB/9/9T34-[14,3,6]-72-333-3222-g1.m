s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[14,3,6]-72-333-3222-g1";
s`BelyiDBFilename := "9T34-[14,3,6]-72-333-3222-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 14, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 4, 7, 8, 5, 1, 3, 9, 6, 2 ],
[ 2, 5, 9, 6, 1, 4, 8, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 1, 9, 8 ],
[ 3, 9, 5, 7, 1, 2, 8, 4, 6 ],
[ 4, 5, 6, 1, 8, 3, 9, 2, 7 ]
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
[ 2, 7, 4, 8, 3, 9, 5, 1, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 3, 4, 2, 9, 8, 1, 6, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 8, 9, 7, 2, 3, 4, 6, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 8, 4, 5, 9, 3, 7, 6, 1, 2 ]
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

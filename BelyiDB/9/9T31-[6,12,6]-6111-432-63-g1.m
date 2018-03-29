s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T31-[6,12,6]-6111-432-63-g1";
s`BelyiDBFilename := "9T31-[6,12,6]-6111-432-63-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 12, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 > |
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
\[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
\[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]:
 Order := 1296 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
\[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
\[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]:
 Order := 1296 >) |
[ PermutationGroup<9 |  
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
\[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
\[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]:
 Order := 1296 > |
[ 4, 5, 2, 9, 1, 6, 7, 8, 3 ],
[ 9, 1, 8, 6, 7, 3, 5, 4, 2 ],
[ 7, 6, 1, 2, 9, 4, 5, 3, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
\[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
\[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]:
 Order := 1296 > |
[ 4, 5, 2, 9, 1, 6, 7, 8, 3 ],
[ 7, 6, 4, 5, 3, 1, 2, 9, 8 ],
[ 4, 5, 8, 6, 7, 2, 1, 9, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 > |
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
[ 7, 6, 4, 5, 3, 9, 1, 2, 8 ],
[ 3, 4, 8, 6, 7, 2, 1, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 1296 > |
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ],
[ 8, 6, 5, 3, 4, 1, 9, 2, 7 ],
[ 5, 3, 8, 7, 6, 2, 9, 1, 4 ]
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

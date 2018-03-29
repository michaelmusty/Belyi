s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T8-[6,6,2]-63-63-22221-g1";
s`BelyiDBFilename := "9T8-[6,6,2]-63-63-22221-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 36 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 8, 6, 4, 5, 3, 1, 2, 9, 7 ],
[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 4, 5, 3, 1, 2, 9, 7 ],
\[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]:
 Order := 36 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 4, 5, 3, 1, 2, 9, 7 ],
\[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 4, 5, 3, 1, 2, 9, 7 ],
\[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]:
 Order := 36 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 6, 7, 5, 3, 4, 2, 9, 1, 8 ],
[ 9, 2, 7, 6, 8, 4, 3, 5, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 36 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 8, 6, 4, 5, 3, 1, 2, 9, 7 ],
[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]
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

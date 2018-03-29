s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T9-[4,4,3]-441-441-333-g1";
s`BelyiDBFilename := "9T9-[4,4,3]-441-441-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 > |
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
\[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ]:
 Order := 36 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
\[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
\[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ]:
 Order := 36 > |
[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 > |
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
[ 9, 4, 3, 7, 2, 1, 5, 6, 8 ],
[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ]
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

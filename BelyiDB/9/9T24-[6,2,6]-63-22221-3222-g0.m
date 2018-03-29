s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T24-[6,2,6]-63-22221-3222-g0";
s`BelyiDBFilename := "9T24-[6,2,6]-63-22221-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 2, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
[ 7, 6, 3, 5, 4, 2, 1, 9, 8 ],
[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 7, 6, 3, 5, 4, 2, 1, 9, 8 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 324 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 7, 6, 3, 5, 4, 2, 1, 9, 8 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 7, 6, 3, 5, 4, 2, 1, 9, 8 ],
\[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]:
 Order := 324 > |
[ 6, 8, 2, 1, 9, 3, 5, 4, 7 ],
[ 3, 5, 1, 9, 2, 6, 8, 7, 4 ],
[ 9, 1, 6, 7, 8, 3, 4, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 > |
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
[ 7, 6, 3, 5, 4, 2, 1, 9, 8 ],
[ 2, 9, 6, 7, 8, 3, 4, 5, 1 ]
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T13-[6,3,2]-63-333-222111-g0";
s`BelyiDBFilename := "9T13-[6,3,2]-63-333-222111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 54 > |
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
\[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]:
 Order := 54 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
\[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
\[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
\[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]:
 Order := 54 > |
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 54 > |
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ],
[ 6, 7, 1, 2, 9, 3, 4, 5, 8 ],
[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ]
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

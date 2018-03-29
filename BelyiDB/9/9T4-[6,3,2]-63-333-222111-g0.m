s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T4-[6,3,2]-63-333-222111-g0";
s`BelyiDBFilename := "9T4-[6,3,2]-63-333-222111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
\[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]:
 Order := 18 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
\[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]:
 Order := 18 >) |
[ PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
\[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ],
[ 1, 9, 5, 4, 3, 8, 7, 6, 2 ]
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

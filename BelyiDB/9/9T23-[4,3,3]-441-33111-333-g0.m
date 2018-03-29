s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T23-[4,3,3]-441-33111-333-g0";
s`BelyiDBFilename := "9T23-[4,3,3]-441-33111-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
[ 7, 5, 3, 1, 8, 6, 4, 2, 9 ],
[ 4, 7, 6, 9, 3, 5, 8, 2, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
\[ 7, 5, 3, 1, 8, 6, 4, 2, 9 ],
\[ 4, 7, 6, 9, 3, 5, 8, 2, 1 ]:
 Order := 216 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
\[ 7, 5, 3, 1, 8, 6, 4, 2, 9 ],
\[ 4, 7, 6, 9, 3, 5, 8, 2, 1 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
\[ 7, 5, 3, 1, 8, 6, 4, 2, 9 ],
\[ 4, 7, 6, 9, 3, 5, 8, 2, 1 ]:
 Order := 216 > |
[ 8, 3, 6, 4, 2, 5, 9, 7, 1 ],
[ 8, 4, 1, 6, 5, 2, 7, 3, 9 ],
[ 9, 5, 6, 2, 4, 8, 1, 3, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 1, 7, 5, 2, 8, 3, 9, 6, 4 ],
[ 7, 5, 3, 1, 8, 6, 4, 2, 9 ],
[ 4, 7, 6, 9, 3, 5, 8, 2, 1 ]
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T27-[7,2,3]-711-22221-333-g0";
s`BelyiDBFilename := "9T27-[7,2,3]-711-22221-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 2, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 2, 6, 5, 4, 1, 9, 7, 3, 8 ],
[ 6, 4, 7, 2, 8, 1, 3, 5, 9 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 6, 5, 4, 1, 9, 7, 3, 8 ],
\[ 6, 4, 7, 2, 8, 1, 3, 5, 9 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 6, 5, 4, 1, 9, 7, 3, 8 ],
\[ 6, 4, 7, 2, 8, 1, 3, 5, 9 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >) |
[ PermutationGroup<9 |  
\[ 2, 6, 5, 4, 1, 9, 7, 3, 8 ],
\[ 6, 4, 7, 2, 8, 1, 3, 5, 9 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 > |
[ 5, 1, 8, 4, 3, 2, 7, 9, 6 ],
[ 3, 9, 1, 6, 7, 4, 5, 8, 2 ],
[ 9, 4, 7, 6, 3, 2, 5, 1, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 >) |
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 2, 6, 5, 4, 1, 9, 7, 3, 8 ],
[ 6, 4, 7, 2, 8, 1, 3, 5, 9 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T22-[6,6,3]-63-63-333-g2";
s`BelyiDBFilename := "9T22-[6,6,3]-63-63-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 6, 8, 2, 1, 9, 4, 3, 5, 7 ],
[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 6, 8, 2, 1, 9, 4, 3, 5, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 162 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 6, 8, 2, 1, 9, 4, 3, 5, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 6, 8, 2, 1, 9, 4, 3, 5, 7 ],
\[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]:
 Order := 162 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 6, 8, 9, 2, 1, 4, 3, 5, 7 ],
[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 6, 8, 2, 1, 9, 4, 3, 5, 7 ],
[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]
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

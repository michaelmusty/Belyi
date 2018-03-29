s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T13-[6,6,3]-63-63-333-g2";
s`BelyiDBFilename := "9T13-[6,6,3]-63-63-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 54 > |
[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
\[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 54 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
\[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
\[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
\[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]:
 Order := 54 > |
[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
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
[ 4, 3, 7, 6, 8, 9, 2, 1, 5 ],
[ 5, 4, 7, 6, 8, 2, 1, 9, 3 ],
[ 5, 3, 6, 7, 8, 2, 9, 1, 4 ]
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

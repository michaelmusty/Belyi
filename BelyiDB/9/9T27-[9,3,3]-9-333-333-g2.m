s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T27-[9,3,3]-9-333-333-g2";
s`BelyiDBFilename := "9T27-[9,3,3]-9-333-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
\[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
\[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >) |
[ PermutationGroup<9 |  
\[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
\[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 > |
[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
[ 5, 4, 9, 7, 8, 3, 2, 1, 6 ],
[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ]
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
[ 6, 5, 9, 7, 4, 8, 3, 2, 1 ],
[ 3, 5, 4, 1, 7, 8, 2, 9, 6 ],
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

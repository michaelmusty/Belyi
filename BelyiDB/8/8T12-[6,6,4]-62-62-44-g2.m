s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T12-[6,6,4]-62-62-44-g2";
s`BelyiDBFilename := "8T12-[6,6,4]-62-62-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 > |
[ 6, 8, 7, 5, 2, 4, 3, 1 ],
[ 2, 7, 1, 8, 6, 3, 5, 4 ],
[ 4, 7, 2, 5, 8, 3, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 8, 7, 5, 2, 4, 3, 1 ],
\[ 2, 7, 1, 8, 6, 3, 5, 4 ],
\[ 4, 7, 2, 5, 8, 3, 6, 1 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 8, 7, 5, 2, 4, 3, 1 ],
\[ 2, 7, 1, 8, 6, 3, 5, 4 ],
\[ 4, 7, 2, 5, 8, 3, 6, 1 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 6, 8, 7, 5, 2, 4, 3, 1 ],
\[ 2, 7, 1, 8, 6, 3, 5, 4 ],
\[ 4, 7, 2, 5, 8, 3, 6, 1 ]:
 Order := 24 > |
[ 6, 8, 7, 5, 2, 4, 3, 1 ],
[ 2, 7, 1, 8, 6, 3, 5, 4 ],
[ 4, 7, 2, 5, 8, 3, 6, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 > |
[ 6, 8, 7, 5, 2, 4, 3, 1 ],
[ 2, 7, 1, 8, 6, 3, 5, 4 ],
[ 4, 7, 2, 5, 8, 3, 6, 1 ]
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

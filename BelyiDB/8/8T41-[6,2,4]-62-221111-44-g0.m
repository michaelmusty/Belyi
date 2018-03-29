s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T41-[6,2,4]-62-221111-44-g0";
s`BelyiDBFilename := "8T41-[6,2,4]-62-221111-44-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 7, 6, 4, 2, 8, 1, 3, 5 ],
[ 1, 2, 8, 7, 5, 6, 4, 3 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 6, 4, 2, 8, 1, 3, 5 ],
\[ 1, 2, 8, 7, 5, 6, 4, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 6, 4, 2, 8, 1, 3, 5 ],
\[ 1, 2, 8, 7, 5, 6, 4, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 7, 6, 4, 2, 8, 1, 3, 5 ],
\[ 1, 2, 8, 7, 5, 6, 4, 3 ],
\[ 6, 7, 4, 8, 3, 2, 1, 5 ]:
 Order := 192 > |
[ 6, 4, 7, 3, 8, 2, 1, 5 ],
[ 1, 3, 2, 5, 4, 6, 7, 8 ],
[ 7, 6, 5, 3, 8, 1, 2, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 3, 2, 1, 5, 6, 7, 4, 8 ]:
 Order := 192 > |
[ 7, 6, 4, 2, 8, 1, 3, 5 ],
[ 1, 2, 8, 7, 5, 6, 4, 3 ],
[ 6, 7, 4, 8, 3, 2, 1, 5 ]
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T1-[8,8,2]-8-8-2222-g2";
s`BelyiDBFilename := "8T1-[8,8,2]-8-8-2222-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 5, 6, 7, 8, 1, 2, 3 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 1, 2, 3 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 1, 2, 3 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 1, 2, 3 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 5, 6, 7, 8, 1, 2, 3 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 4, 5, 6, 7, 8, 1, 2, 3 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
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

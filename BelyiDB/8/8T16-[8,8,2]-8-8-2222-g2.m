s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T16-[8,8,2]-8-8-2222-g2";
s`BelyiDBFilename := "8T16-[8,8,2]-8-8-2222-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 32 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 3, 8, 1, 6, 7, 4, 5 ],
[ 3, 4, 1, 2, 7, 8, 5, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 3, 8, 1, 6, 7, 4, 5 ],
\[ 3, 4, 1, 2, 7, 8, 5, 6 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 3, 8, 1, 6, 7, 4, 5 ],
\[ 3, 4, 1, 2, 7, 8, 5, 6 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 3, 8, 1, 6, 7, 4, 5 ],
\[ 3, 4, 1, 2, 7, 8, 5, 6 ]:
 Order := 32 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 3, 8, 1, 6, 7, 4, 5 ],
[ 3, 4, 1, 2, 7, 8, 5, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 32 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 3, 8, 1, 6, 7, 4, 5 ],
[ 3, 4, 1, 2, 7, 8, 5, 6 ]
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

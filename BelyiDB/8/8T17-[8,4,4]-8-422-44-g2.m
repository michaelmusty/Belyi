s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T17-[8,4,4]-8-422-44-g2";
s`BelyiDBFilename := "8T17-[8,4,4]-8-422-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 32 > |
[ 7, 4, 5, 1, 2, 3, 8, 6 ],
[ 3, 8, 1, 5, 6, 7, 4, 2 ],
[ 7, 4, 5, 8, 1, 2, 3, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 8, 1, 2, 7, 4, 5, 6, 3 ]:
 Order := 4 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 8, 1, 2, 7, 4, 5, 6, 3 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 4, 5, 1, 2, 3, 8, 6 ],
\[ 3, 8, 1, 5, 6, 7, 4, 2 ],
\[ 7, 4, 5, 8, 1, 2, 3, 6 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 4, 5, 1, 2, 3, 8, 6 ],
\[ 3, 8, 1, 5, 6, 7, 4, 2 ],
\[ 7, 4, 5, 8, 1, 2, 3, 6 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 7, 4, 5, 1, 2, 3, 8, 6 ],
\[ 3, 8, 1, 5, 6, 7, 4, 2 ],
\[ 7, 4, 5, 8, 1, 2, 3, 6 ]:
 Order := 32 > |
[ 7, 4, 5, 1, 2, 3, 8, 6 ],
[ 3, 8, 1, 5, 6, 7, 4, 2 ],
[ 7, 4, 5, 8, 1, 2, 3, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 32 > |
[ 7, 4, 5, 1, 2, 3, 8, 6 ],
[ 3, 8, 1, 5, 6, 7, 4, 2 ],
[ 7, 4, 5, 8, 1, 2, 3, 6 ]
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

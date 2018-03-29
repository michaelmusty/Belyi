s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T7-[8,8,4]-8-8-44-g3";
s`BelyiDBFilename := "8T7-[8,8,4]-8-8-44-g3.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 3, 8, 5, 2, 7, 4, 1 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 7, 8, 1, 2, 3, 4, 5, 6 ]:
 Order := 4 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 7, 8, 1, 2, 3, 4, 5, 6 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 6, 3, 8, 5, 2, 7, 4, 1 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ]:
 Order := 16 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 6, 3, 8, 5, 2, 7, 4, 1 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ]:
 Order := 16 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 6, 3, 8, 5, 2, 7, 4, 1 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ]:
 Order := 16 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 2, 7, 4, 1, 6, 3, 8, 5 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 5, 2, 7, 4, 1, 6, 3, 8 ]:
 Order := 16 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 6, 3, 8, 5, 2, 7, 4, 1 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ]
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

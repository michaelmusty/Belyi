s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,10,2]-611-521-2222-g0";
s`BelyiDBFilename := "8T50-[6,10,2]-611-521-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 10, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 3, 8, 7, 6, 5, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 3, 8, 7, 6, 5, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 3, 8, 7, 6, 5, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8 ],
\[ 3, 8, 7, 6, 5, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 3, 8, 7, 6, 5, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 3, 8, 7, 6, 5, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
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

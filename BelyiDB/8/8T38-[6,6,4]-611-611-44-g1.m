s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T38-[6,6,4]-611-611-44-g1";
s`BelyiDBFilename := "8T38-[6,6,4]-611-611-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 6, 7, 5, 4, 2, 3, 1, 8 ],
[ 6, 8, 3, 5, 2, 4, 7, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 7, 5, 4, 2, 3, 1, 8 ],
\[ 6, 8, 3, 5, 2, 4, 7, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 7, 5, 4, 2, 3, 1, 8 ],
\[ 6, 8, 3, 5, 2, 4, 7, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 6, 7, 5, 4, 2, 3, 1, 8 ],
\[ 6, 8, 3, 5, 2, 4, 7, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ]:
 Order := 192 > |
[ 6, 7, 5, 4, 2, 3, 1, 8 ],
[ 6, 8, 3, 5, 2, 4, 7, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 6, 7, 5, 4, 2, 3, 1, 8 ],
[ 6, 8, 3, 5, 2, 4, 7, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
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
